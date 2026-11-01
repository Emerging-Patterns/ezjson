# proofs of laws/BuiltValuesWellFormed.bend
import Base
import ../src/value.bend as V
import ../src/lazy.bend as Lazy
import ../laws/BuiltValuesWellFormed.bend as Laws
import ./lemmas/LexemeOrder.bend as M1
import ./lemmas/ParserStateCloses.bend as M2

def Laws.wf_scalars(_flag, _txt):
  {==}

# num.go builds a well-formed value whatever its check answered
law wf_num_go:
  for +txt: String
  for ok: Bool
  for h_ok: {V.num.ok(txt) == ok : Bool}
  {V.wf(V.num.go(txt, ok)) == True{} : Bool}

def wf_num_go(_txt, ok, h_ok):
  match ok:
    case True{}:
      h_ok
    case False{}:
      {==}

def Laws.wf_num(txt):
  wf_num_go(txt, V.num.ok(txt), {==})

# the cells arr.go builds from well-formed values are a well-formed array
law wf_arr_go:
  for +xs: List<&2, V.Json>
  for +h_all: {Laws.all_wf(xs) == True{} : Bool}
  {V.wf.go(V.arr.go(xs), V.WArr{}) == True{} : Bool}

def wf_arr_go(xs, h_all):
  match xs:
    case Nil{}:
      {==}
    case hd <> tl:
      hl = Equal.sym(Bool, V.wf(hd), True{}, M1.and_left(V.wf(hd), Laws.all_wf(tl), h_all))
      %hl : {Lazy.stop(Bool, Bool.not(_), False{}, _u => V.wf.go(V.arr.go(tl), V.WArr{})) == True{} : Bool}
      wf_arr_go(tl, M1.and_right(V.wf(hd), Laws.all_wf(tl), h_all))

def Laws.wf_arr(xs, h_all):
  wf_arr_go(xs, h_all)

# one step of wf_obj_go: the head's value, and the rest by the hypothesis ih
law wf_obj_cons:
  for -vv: V.Json
  for -tl: List<&1, String & V.Json>
  for got: ({V.wf(vv) == True{} : Bool} & {Laws.all_wf_pairs(tl) == True{} : Bool})
  for ih: {Laws.all_wf_pairs(tl) == True{} : Bool} -> {V.wf.go(V.obj.go(tl), V.WObj{}) == True{} : Bool}
  {Lazy.stop(Bool, Bool.not(V.wf(vv)), False{}, _u => V.wf.go(V.obj.go(tl), V.WObj{})) == True{} : Bool}

def wf_obj_cons(vv, tl, got, ih):
  (el, er) = got
  hl = Equal.sym(Bool, V.wf(vv), True{}, el)
  %hl : {Lazy.stop(Bool, Bool.not(_), False{}, _u => V.wf.go(V.obj.go(tl), V.WObj{})) == True{} : Bool}
  ih(er)

# the cells obj.go builds from well-formed values are a well-formed object
law wf_obj_go:
  for ps: List<&1, String & V.Json>
  for h_all: {Laws.all_wf_pairs(ps) == True{} : Bool}
  {V.wf.go(V.obj.go(ps), V.WObj{}) == True{} : Bool}

def wf_obj_go(ps, h_all):
  match ps:
    case Nil{}:
      {==}
    case (_kk, vv) <> tl:
      wf_obj_cons(vv, tl, M1.and_both(V.wf(vv), Laws.all_wf_pairs(tl), h_all), hh => wf_obj_go(tl, hh))

def Laws.wf_obj(ps, h_all):
  wf_obj_go(ps, h_all)
