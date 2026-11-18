import ControlFlow

namespace ControlFlow.Tests

abbrev DominatorTestResult := Option (List (Nat × List Nat))
def validateDominator (cfg : CFG Nat Digraph.FuncGraphType)
    (results? : DominatorTestResult)
    : Except String Unit := do
  match results?, Dom.Algorithm.compute cfg with
  | .none, .none => return
  | .none, .some _ => throw s!"Expected dominators to return none!"
  | .some results, .none => throw s!"Expected dominators to return ${results}"
  | .some results, .some cresult =>
    let ⟨sdom, dom, _⟩ := cresult
    -- let idom := Dom.Algorithm.get_immediate_dominator cresult
    -- let dom_frontier := Dom.Algorithm.get_dominance_frontier cfg idom |>.get!
    -- let idomStr := Digraph.verticesToString
    --   (Digraph.toVertices cfg.digraph)
    --   (fun v => idom v |>.toList)
    -- let frontierStr := Digraph.verticesToString
    --   (Digraph.toVertices cfg.digraph)
    --   (fun v => dom_frontier v |>.toList)
    -- dbg_trace "idoms"
    -- dbg_trace idomStr
    -- dbg_trace "frontier"
    -- dbg_trace frontierStr
    results.foldlM (fun _ (v, expectedSDom) => do
      if sdom v |>.beq (Std.HashSet.ofList expectedSDom) then
        if dom v |>.beq (Std.HashSet.ofList (v::expectedSDom)) then
          return
        else throw s!"Node {v} has incorrect doms\nExpected {v::expectedSDom}\nGot {dom v}"
      else throw s!"Node {v} has incorrect sdoms\nExpected {expectedSDom}\nGot {sdom v}"
    ) ()
def runDomTest
    (name : String)
    (cfg : CFG Nat Digraph.FuncGraphType)
    (results? : DominatorTestResult) : IO Bool := do
  match validateDominator cfg results? with
  | .ok _ =>
    println! s!"✓ Passed {name}"
    return true
  | .error e =>
    println! s!"× Failed {name}\n{e}"
    return false

def straightCFG := Digraph.FuncGraph.empty (α := Nat)
  |>.add_edge (1, 2)
  |>.add_edge (2, 3)
  |>.add_edge (3, 4)
  |>.add_edge (4, 5)
  |>.add_edge (5, 6)
  |> (CFG.mk · ⟨1, sorry⟩ sorry)
def straightCFG.results : DominatorTestResult := .some ([
  (1, [2, 3, 4, 5, 6]),
  (2, [3, 4, 5, 6]),
  (3, [4, 5, 6]),
  (4, [5, 6]),
  (5, [6]),
  (6, []),
])

def ifCFG := Digraph.FuncGraph.empty (α := Nat)
  |>.add_edge (1, 2)
  |>.add_edge (1, 3)
  |>.add_edge (2, 4)
  |>.add_edge (3, 4)
  |>.add_edge (4, 5)
  |> (CFG.mk · ⟨1, sorry⟩ sorry)
def ifCFG.results : DominatorTestResult := .some ([
  (1, [2, 3, 4, 5]),
  (2, []),
  (3, []),
  (4, [5]),
  (5, []),
])

def whileCFG := Digraph.FuncGraph.empty (α := Nat)
  |>.add_edge (1, 2)
  |>.add_edge (2, 3)
  |>.add_edge (2, 4)
  |>.add_edge (3, 2)
  |>.add_edge (4, 5)
  |> (CFG.mk · ⟨1, sorry⟩ sorry)
def whileCFG.results : DominatorTestResult := .some ([
  (1, [2, 3, 4, 5]),
  (2, [3, 4, 5]),
  (3, []),
  (4, [5]),
  (5, []),
])

def whileifCFG := Digraph.FuncGraph.empty (α := Nat)
  |>.add_edge (1, 2)
  |>.add_edge (2, 3)
  |>.add_edge (2, 7)
  |>.add_edge (3, 4)
  |>.add_edge (3, 5)
  |>.add_edge (4, 6)
  |>.add_edge (5, 6)
  |>.add_edge (6, 2)
  |> (CFG.mk · ⟨1, sorry⟩ sorry)
def whileifCFG.results : DominatorTestResult := .some ([
  (1, [2, 3, 4, 5, 6, 7]),
  (2, [3, 4, 5, 6, 7]),
  (3, [4, 5, 6]),
  (4, []),
  (5, []),
  (6, []),
  (7, []),
])

-- https://en.wikipedia.org/wiki/Dominator_(graph_theory)
def wikiDominatorCFG := Digraph.FuncGraph.empty (α := Nat)
  |>.add_edge (1, 2)
  |>.add_edge (2, 3)
  |>.add_edge (2, 4)
  |>.add_edge (2, 6)
  |>.add_edge (3, 5)
  |>.add_edge (4, 5)
  |>.add_edge (5, 2)
  |> (CFG.mk · ⟨1, sorry⟩ sorry)
def wikiDominatorCFG.results : DominatorTestResult := .some ([
  (1, [2, 3, 4, 5, 6]),
  (2, [3, 4, 5, 6]),
  (3, []),
  (4, []),
  (5, []),
  (6, []),
])

def weirdCFG := Digraph.FuncGraph.empty (α := Nat)
  |>.add_edge (0, 1)
  |>.add_edge (1, 2)
  |>.add_edge (1, 3)
  |>.add_edge (2, 3)
  |>.add_edge (2, 6)
  |>.add_edge (3, 4)
  |>.add_edge (4, 5)
  |>.add_edge (6, 7)
  |>.add_edge (7, 5)
  |> (CFG.mk · ⟨0, sorry⟩ sorry)
def weirdCFG.results : DominatorTestResult := .some ([
  (0, [1, 2, 3, 4, 5, 6, 7]),
  (1, [2, 3, 4, 5, 6, 7]),
  (2, [6, 7]),
  (3, [4]),
  (4, []),
  (5, []),
  (6, [7]),
  (7, []),
])
/- idom
  0 | -
  1 | 0
  2 | 1
  3 | 1
  4 | 3
  5 | 1
  6 | 2
  7 | 6
-/

def weird2CFG := Digraph.FuncGraph.empty (α := Nat)
  |>.add_edge (0, 1)
  |>.add_edge (1, 2)
  |>.add_edge (0, 2)
  |>.add_edge (2, 3)
  |>.add_edge (3, 2)
  |>.add_edge (3, 4)
  |>.add_edge (3, 5)
  |>.add_edge (4, 6)
  |>.add_edge (5, 0)
  |>.add_edge (5, 6)
  |>.add_edge (6, 7)
  |>.add_edge (7, 8)
  |>.add_edge (7, 9)
  |>.add_edge (8, 2)
  |>.add_edge (9, 6)
  |> (CFG.mk · ⟨0, sorry⟩ sorry)
def weird2CFG.results : DominatorTestResult := .some ([
  (0, [1, 2, 3, 4, 5, 6, 7, 8, 9]),
  (1, []),
  (2, [3, 4, 5, 6, 7, 8, 9]),
  (3, [4, 5, 6, 7, 8, 9]),
  (4, []),
  (5, []),
  (6, [7, 8, 9]),
  (7, [8, 9]),
  (8, []),
  (9, []),
])
/- idom
  0 | -
  1 | 0
  2 | 0
  3 | 2
  4 | 3
  5 | 3
  6 | 3
  7 | 6
  8 | 7
  9 | 7
-/

def weird3CFG := Digraph.FuncGraph.empty (α := Nat)
  |>.add_edge (0, 1)
  |>.add_edge (0, 2)
  |>.add_edge (1, 3)
  |>.add_edge (2, 7)
  |>.add_edge (2, 8)
  |>.add_edge (3, 4)
  |>.add_edge (4, 3)
  |>.add_edge (4, 5)
  |>.add_edge (5, 6)
  |>.add_edge (6, 5)
  |>.add_edge (7, 6)
  |>.add_edge (8, 6)
  |>.add_edge (8, 9)
  |>.add_edge (9, 6)
  |> (CFG.mk · ⟨0, sorry⟩ sorry)
def weird3CFG.results : DominatorTestResult := .some ([
  (0, [1, 2, 3, 4, 5, 6, 7, 8, 9]),
  (1, [3, 4]),
  (2, [7, 8, 9]),
  (3, [4]),
  (4, []),
  (5, []),
  (6, []),
  (7, []),
  (8, [9]),
  (9, []),
])
/- idom
  0 | -
  1 | 0
  2 | 0
  3 | 1
  4 | 3
  5 | 0
  6 | 0
  7 | 2
  8 | 2
  9 | 8
-/

end ControlFlow.Tests

open ControlFlow.Tests in
def main : IO Unit := do
  println! "Dominator Tests"
  let _ ← runDomTest "straight" straightCFG straightCFG.results
  let _ ← runDomTest "if" ifCFG ifCFG.results
  let _ ← runDomTest "while" whileCFG whileCFG.results
  let _ ← runDomTest "whileif" whileifCFG whileifCFG.results
  let _ ← runDomTest "wikipedia" wikiDominatorCFG wikiDominatorCFG.results
  let _ ← runDomTest "weird" weirdCFG weirdCFG.results
  let _ ← runDomTest "weird2" weird2CFG weird2CFG.results
  let _ ← runDomTest "weird3" weird3CFG weird3CFG.results
  return

