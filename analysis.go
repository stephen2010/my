/*
go/build/build.go
779	// testImported := make(map[string][]token.Position)
780	// xTestImported := make(map[string][]token.Position)
				if isXTest {
915					// xTestImported[path] = append(xTestImported[path], fset.Position(spec.Pos()))
				} else if isTest {
917					// testImported[path] = append(testImported[path], fset.Position(spec.Pos()))
		} else if isXTest {
947			// p.XTestGoFiles = append(p.XTestGoFiles, name)
		} else if isTest {
949			// p.TestGoFiles = append(p.TestGoFiles, name)
967	// p.TestImports, p.TestImportPos = cleanImports(testImported)
968	// p.XTestImports, p.XTestImportPos = cleanImports(xTestImported)


ps -C fenxihttp | grep "fenxi"
ps -C 12 | grep "12"
kill -INT 7153
*/

package analysis

import (
	"fmt"
	"go/build"
	"go/token"
	"go/types"
	"html"
	"io"
	"log"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"sync"

	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

// -- links ------------------------------------------------------------

type Link interface {
	Where() string
	Start() int
	// End() int
	Onclick() int
	HrefOnclick() MoshiMode
	Href() string
	// Line() int
	// Column() int
	// Write(w io.Writer, _ int, start bool) // the godoc.LinkWriter signature
}

type MoshiMode int

const (
	MoshiHref MoshiMode = iota
	MoshiOnclick
)

type aLink struct {
	where                            string
	start/*, end, line, column*/ int // =godoc.Segment
	title                            string // hover text
	hrefonlick                       MoshiMode
	onclick                          int    // JS code (NB: trusted)
	href                             string // URL     (NB: trusted)
}

func (a aLink) Where() string { return a.where }

func (a aLink) Start() int { return a.start }

// func (a aLink) End() int               { return a.end }
func (a aLink) Onclick() int           { return a.onclick }
func (a aLink) HrefOnclick() MoshiMode { return a.hrefonlick }
func (a aLink) Href() string           { return a.href }

// func (a aLink) Line() int              { return a.line }
// func (a aLink) Column() int            { return a.column }

/*
func (a aLink) Write(w io.Writer, _ int, start bool) {
	if start {
		fmt.Fprintf(w, `<a title='%s'`, html.EscapeString(a.title))
		if a.onclick != "" {
			fmt.Fprintf(w, ` onclick='%s'`, html.EscapeString(a.onclick))
		}
		if a.href != "" {
			// TODO(adonovan): I think that in principle, a.href must first be
			// url.QueryEscape'd, but if I do that, a leading slash becomes "%2F",
			// which causes the browser to treat the path as relative, not absolute.
			// WTF?
			fmt.Fprintf(w, ` href='%s'`, html.EscapeString(a.href))
		}
		fmt.Fprintf(w, ">")
	} else {
		fmt.Fprintf(w, "</a>")
	}
}
*/

type errorLink struct {
	start int
	msg   string
}

func (e errorLink) Where() string { return "" }

func (e errorLink) Start() int { return e.start }

// func (e errorLink) End() int               { return e.start + 1 }
func (e errorLink) Onclick() int           { return 0 }
func (a errorLink) HrefOnclick() MoshiMode { return MoshiMode(0) }
func (a errorLink) Href() string           { return "" }

// func (a errorLink) Line() int              { return 0 }
// func (a errorLink) Column() int            { return 0 }

func (e errorLink) Write(w io.Writer, _ int, start bool) {
	// <span> causes havoc, not sure why, so use <a>.
	if start {
		fmt.Fprintf(w, `<a class='error' title='%s'>`, html.EscapeString(e.msg))
	} else {
		fmt.Fprintf(w, "</a>")
	}
}

// -- fileInfo ---------------------------------------------------------

// FileInfo holds analysis information for the source file view.
// Clients must not mutate it.
type FileInfo struct {
	Data  []interface{} // JSON serializable values
	Links []Link        // HTML link markup
}

// A fileInfo is the server's store of hyperlinks and JSON data for a
// particular file.
type fileInfo struct {
	mu        sync.Mutex
	data      []interface{} // JSON objects
	links     []Link
	sorted    bool
	hasErrors bool // TODO(adonovan): surface this in the UI
}

// addLink adds a link to the Go source file fi.
func (fi *fileInfo) addLink(link Link) {
	fi.mu.Lock()
	fi.links = append(fi.links, link)
	fi.sorted = false
	if _, ok := link.(errorLink); ok {
		fi.hasErrors = true
	}
	fi.mu.Unlock()
}

// addData adds the structured value x to the JSON data for the Go
// source file fi.  Its index is returned.
func (fi *fileInfo) addData(x interface{}) int {
	fi.mu.Lock()
	index := len(fi.data)
	fi.data = append(fi.data, x)
	fi.mu.Unlock()
	return index
}

// get returns the file info in external form.
// Callers must not mutate its fields.
func (fi *fileInfo) get() FileInfo {
	var r FileInfo
	// Copy slices, to avoid races.
	fi.mu.Lock()
	r.Data = append(r.Data, fi.data...)
	if !fi.sorted {
		sort.Sort(linksByStart(fi.links))
		fi.sorted = true
	}
	r.Links = append(r.Links, fi.links...)
	fi.mu.Unlock()
	return r
}

// PackageInfo holds analysis information for the package view.
// Clients must not mutate it.
type PackageInfo struct {
	CallGraph      []*PCGNodeJSON
	CallGraphIndex map[string]int
	Types          []*TypeInfoJSON
}

type pkgInfo struct {
	mu             sync.Mutex
	callGraph      []*PCGNodeJSON
	callGraphIndex map[string]int  // keys are (*ssa.Function).RelString()
	types          []*TypeInfoJSON // type info for exported types
}

func (pi *pkgInfo) setCallGraph(callGraph []*PCGNodeJSON, callGraphIndex map[string]int) {
	pi.mu.Lock()
	pi.callGraph = callGraph
	pi.callGraphIndex = callGraphIndex
	pi.mu.Unlock()
}

func (pi *pkgInfo) addType(t *TypeInfoJSON) {
	pi.mu.Lock()
	pi.types = append(pi.types, t)
	pi.mu.Unlock()
}

// get returns the package info in external form.
// Callers must not mutate its fields.
func (pi *pkgInfo) get() PackageInfo {
	var r PackageInfo
	// Copy slices, to avoid races.
	pi.mu.Lock()
	r.CallGraph = append(r.CallGraph, pi.callGraph...)
	r.CallGraphIndex = pi.callGraphIndex
	r.Types = append(r.Types, pi.types...)
	pi.mu.Unlock()
	return r
}

// -- Result -----------------------------------------------------------

// Result contains the results of analysis.
// The result contains a mapping from filenames to a set of HTML links
// and JavaScript data referenced by the links.
type Result struct {
	mu        sync.Mutex           // guards maps (but not their contents)
	status    string               // global analysis status
	fileInfos map[string]*fileInfo // keys are godoc file URLs
	pkgInfos  map[string]*pkgInfo  // keys are import paths
}

// fileInfo returns the fileInfo for the specified godoc file URL,
// constructing it as needed.  Thread-safe.
func (res *Result) fileInfo(url string) *fileInfo {
	res.mu.Lock()
	fi, ok := res.fileInfos[url]
	if !ok {
		if res.fileInfos == nil {
			res.fileInfos = make(map[string]*fileInfo)
		}
		fi = new(fileInfo)
		res.fileInfos[url] = fi
	}
	res.mu.Unlock()
	return fi
}

// Status returns a human-readable description of the current analysis status.
func (res *Result) Status() string {
	res.mu.Lock()
	defer res.mu.Unlock()
	return res.status
}

func (res *Result) setStatusf(format string, args ...interface{}) {
	res.mu.Lock()
	res.status = fmt.Sprintf(format, args...)
	log.Printf(format, args...)
	res.mu.Unlock()
}

// FileInfo returns new slices containing opaque JSON values and the
// HTML link markup for the specified godoc file URL.  Thread-safe.
// Callers must not mutate the elements.
// It returns "zero" if no data is available.
//
func (res *Result) FileInfo(url string) (fi FileInfo) {
	return res.fileInfo(url).get()
}

// pkgInfo returns the pkgInfo for the specified import path,
// constructing it as needed.  Thread-safe.
func (res *Result) pkgInfo(importPath string) *pkgInfo {
	res.mu.Lock()
	pi, ok := res.pkgInfos[importPath]
	if !ok {
		if res.pkgInfos == nil {
			res.pkgInfos = make(map[string]*pkgInfo)
		}
		pi = new(pkgInfo)
		res.pkgInfos[importPath] = pi
	}
	res.mu.Unlock()
	return pi
}

// PackageInfo returns new slices of JSON values for the callgraph and
// type info for the specified package.  Thread-safe.
// Callers must not mutate its fields.
// PackageInfo returns "zero" if no data is available.
//
func (res *Result) PackageInfo(importPath string) PackageInfo {
	return res.pkgInfo(importPath).get()
}

// -- analysis ---------------------------------------------------------

type analysis struct {
	result    *Result
	prog      *ssa.Program
	ops       []chanOp       // all channel ops in program
	allNamed  []*types.Named // all "defined" (formerly "named") types in the program
	ptaConfig pointer.Config
	path2url  map[string]string // maps openable path to godoc file URL (/src/fmt/print.go)
	pcgs      map[*ssa.Package]*packageCallGraph
	usesByObj map[string][]string
	mapObj    map[string]token.Pos
}

// fileAndOffset returns the file and offset for a given pos.
func (a *analysis) fileAndOffset(pos token.Pos) (fi *fileInfo, offset int) {
	return a.fileAndOffsetPosn(a.prog.Fset.Position(pos))
}

// fileAndOffsetPosn returns the file and offset for a given position.
func (a *analysis) fileAndOffsetPosn(posn token.Position) (fi *fileInfo, offset int) {
	url := a.path2url[posn.Filename]
	return a.result.fileInfo(url), posn.Offset
}

// posURL returns the URL of the source extent [pos, pos+len).
func (a *analysis) posURL(pos token.Pos, _ int) string {
	if pos == token.NoPos {
		return ""
	}
	posn := a.prog.Fset.Position(pos)
	// url := a.path2url[posn.Filename]
	return fmt.Sprintf("%s:%d:%d:", posn.Filename, posn.Line, posn.Column)
}

func (a *analysis) posURL2(pos token.Pos) (string, token.Position) {
	if pos == token.NoPos {
		return "", token.Position{}
	}
	posn := a.prog.Fset.Position(pos)
	// url := a.path2url[posn.Filename]
	return fmt.Sprintf("%s:%d:%d:", posn.Filename, posn.Line, posn.Column), posn
}

func (a *analysis) posURL3(pos token.Pos) string {
	if pos == token.NoPos {
		return ""
	}
	posn := a.prog.Fset.Position(pos)
	// url := a.path2url[posn.Filename]
	return fmt.Sprintf("%s:%d:%d:", posn.Filename, posn.Line, posn.Column)
}

// ----------------------------------------------------------------------

// Run runs program analysis and computes the resulting markup,
// populating *result in a thread-safe manner, first with type
// information then later with pointer analysis information if
// enabled by the pta flag.
//
func Run(pta bool, result *Result) {
	conf := loader.Config{
		AllowErrors: true,
	}
	conf.TypeChecker.Error = func(e error) {}

	var /*roots,*/ args []string // roots[i] ends with os.PathSeparator
	vargoroot := filepath.Join(build.Default.GOROOT, "src") + string(os.PathSeparator)
	/*
		roots = append(roots, vargoroot)
		args = allPackages(vargoroot)
		args = append(args, vargoroot+"bufio", vargoroot+"bytes")
		for i, dir := range filepath.SplitList(build.Default.GOPATH) {
			vargopath := filepath.Join(dir, "src") + string(os.PathSeparator)
			// roots = append(roots, vargopath)
			pkgs := allPackages(vargopath)
			log.Printf("GOPATH[%d]=%s: %s\n", i, vargopath, pkgs)
			args = append(args, pkgs...)
		}
	*/
	// args = []string{"golang.org/x/tools/cmd/godoc"}
	//args = []string{"fmt"}
	args = []string{"bytes"}//"c0"} //, , 
	// args = []string{"github.com/gorilla/websocket"}//"github.com/gorilla/websocket/examples/echo"}//"github.com/lucas-clemente/quic-go/example"}
	log.Printf("GOROOT=%s: %s\n", vargoroot, args)

	if _, err := conf.FromArgs(args, false); err != nil {
		result.setStatusf("Analysis failed: %s.", err)
		return
	}

	result.setStatusf("Loading and type-checking packages...")
	iprog, err := conf.Load()
	if iprog != nil {
		for _, info := range iprog.AllPackages {
			for _, err := range info.Errors {
				fmt.Fprintln(os.Stderr, err)
				break
			}
		}
		log.Printf("Loaded %d packages.", len(iprog.AllPackages))
	}
	if err != nil {
		result.setStatusf("Loading failed: %s.\n", err)
		return
	}

	prog := ssautil.CreateProgram(iprog, ssa.GlobalDebug)
	/*
		for _, pkg := range prog.AllPackages() {
			if testmain := prog.CreateTestMainPackage(pkg); testmain != nil {
				log.Printf("Adding tests for %s", pkg.Pkg.Path())
			}
		}
	*/
	result.setStatusf("Constructing SSA form...")
	prog.Build()
	log.Print("SSA construction complete")

	a := analysis{
		result:    result,
		prog:      prog,
		pcgs:      make(map[*ssa.Package]*packageCallGraph),
		usesByObj: make(map[string][]string),
		mapObj:    make(map[string]token.Pos),
	}
	/*
		a.path2url = make(map[string]string)
		for _, info := range iprog.AllPackages {
		nextfile:
			for _, f := range info.Files {
				if f.Pos() == 0 {
					continue
				}
				abs := iprog.Fset.File(f.Pos()).Name()
				// for _, root := range roots {
				rel := strings.TrimPrefix(abs, vargoroot)
				if len(rel) < len(abs) {
					a.path2url[abs] = filepath.ToSlash(rel)
					continue nextfile
				}
				// }

				log.Printf("Can't locate file %s (package %q) beneath any root",
					abs, info.Pkg.Path())
			}
		}

		errors := make(map[token.Position][]string)
		for _, info := range iprog.AllPackages {
			for _, err := range info.Errors {
				switch err := err.(type) {
				case types.Error:
					posn := a.prog.Fset.Position(err.Pos)
					errors[posn] = append(errors[posn], err.Msg)
				case scanner.ErrorList:
					for _, e := range err {
						errors[e.Pos] = append(errors[e.Pos], e.Msg)
					}
				default:
					log.Printf("Package %q has error (%T) without position: %v\n",
						info.Pkg.Path(), err, err)
				}
			}
		}
		for posn, errs := range errors {
			fi, offset := a.fileAndOffsetPosn(posn)
			fi.addLink(errorLink{
				start: offset,
				msg:   strings.Join(errs, "\n"),
			})
		}

		errorType := types.Universe.Lookup("error").Type().(*types.Named)
		a.allNamed = append(a.allNamed, errorType)
		for _, info := range iprog.AllPackages {
			for _, obj := range info.Defs {
				if obj, ok := obj.(*types.TypeName); ok {
					if named, ok := obj.Type().(*types.Named); ok {
						a.allNamed = append(a.allNamed, named)
					}
				}
			}
		}
	*/

	log.Print("Computing implements relation...")
	// facts := computeImplements(&a.prog.MethodSets, a.allNamed)

	log.Print("Extracting type info...")
	for _, info := range iprog.AllPackages {
		// a.doTypeInfo(info, facts)
		a.doTypeInfo3(info)
	}

	for i, jj := range a.usesByObj {
		sort.Strings(jj)
		a.usesByObj[i] = jj
	}
	for objhref, objpos := range a.mapObj {
		str := strings.Join(a.usesByObj[objhref], "<br>")
		posn := a.prog.Fset.Position(objpos)
		fi := a.result.fileInfo(posn.Filename)
		fi.addLink(aLink{
			where: objhref + " info.Uses obj", //fmt.Sprintf("%s:%d:%d: info.Uses", posn.Filename, posn.Line, posn.Column),
			start: posn.Offset,
			// end:        posn.Offset + len(id.Name),
			// line:       posn.Line,
			// column:     posn.Column,
			// title:      types.ObjectString(obj, qualifier),
			hrefonlick: MoshiHref,
			href:       str,
		})
	}

	a.visitInstrs(pta)

	result.setStatusf("Type analysis complete.")

	if pta {
		mainPkgs := ssautil.MainPackages(prog.AllPackages())
		log.Print("Transitively error-free main packages: ", mainPkgs)
		a.pointer(mainPkgs)
	}
}

func (a *analysis) visitInstrs(pta bool) {
	log.Print("Visit instructions...")
	for fn := range ssautil.AllFunctions(a.prog) {
		for _, b := range fn.Blocks {
			for _, instr := range b.Instrs {
				if site, ok := instr.(ssa.CallInstruction); ok {
					if callee := site.Common().StaticCallee(); callee != nil {
						if site.Common().Pos() != token.NoPos {
							a.addCallees(site, []*ssa.Function{callee})
						}
					}
				}

				if !pta {
					continue
				}
				for _, op := range chanOps(instr) {
					a.ops = append(a.ops, op)
					a.ptaConfig.AddQuery(op.ch)
				}
			}
		}
	}
	log.Print("Visit instructions complete")
}

func (a *analysis) pointer(mainPkgs []*ssa.Package) {
	a.ptaConfig.Mains = mainPkgs
	a.ptaConfig.BuildCallGraph = true
	a.ptaConfig.Reflection = false

	a.result.setStatusf("Pointer analysis running...")

	ptares, err := pointer.Analyze(&a.ptaConfig)
	if err != nil {
		a.result.setStatusf("Pointer analysis failed: %s.", err)
		return
	}
	log.Print("Pointer analysis complete.")

	a.result.setStatusf("Computing channel peers...")
	a.doChannelPeers(ptares.Queries)
	a.result.setStatusf("Computing dynamic call graph edges...")
	a.doCallgraph(ptares.CallGraph)

	a.result.setStatusf("Analysis complete.")
}

type linksByStart []Link

func (a linksByStart) Less(i, j int) bool { return a[i].Start() < a[j].Start() }
func (a linksByStart) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a linksByStart) Len() int           { return len(a) }

func allPackages(root string) []string {
	var pkgs []string
	filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if info == nil {
			return nil
		}
		if !info.IsDir() {
			return nil
		}
		base := filepath.Base(path)
		if base == "testdata" || strings.HasPrefix(base, ".") {
			return filepath.SkipDir
		}
		pkg := filepath.ToSlash(strings.TrimPrefix(path, root))
		switch pkg {
		case "builtin":
			return filepath.SkipDir
		case "":
			return nil
		}
		pkgs = append(pkgs, pkg)
		return nil
	})
	return pkgs
}
