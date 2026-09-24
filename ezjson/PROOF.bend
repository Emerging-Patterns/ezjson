# ezjson: the proofs. `bend ezjson/PROOF.bend` is the gate.
import Base
import ./value.bend as V
import ./main.bend as Ezjson
import ./lazy.bend as Lazy
import ./print.bend as Print
import ./LAWS.bend as Laws

# Unit for True, Empty for False: tells them apart
def true_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Empty
    case True{}:
      Unit

# True is never False
law true_false:
  for e: {True{} == False{} : Bool}
  Empty

def true_false(e):
  %e : true_ty(_)
  Unit{}

def Laws.as_bool_bool(_flag):
  {==}

def Laws.as_str_str(_txt):
  {==}

def Laws.as_num_num(txt, h_ok):
  ok = Equal.sym(Bool, V.num.ok(txt), True{}, h_ok)
  %ok : {Ezjson.as_num(V.num.go(txt, _)) == Some{txt} : Maybe<&2, String>}
  {==}

def Laws.as_bool_kind(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{_}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.as_str_kind(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{_}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.as_num_kind(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{_}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.as_u32_kind(val, h_kind):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{raw}:
      Empty.absurd({Ezjson.as_u32(V.JNum{raw}) == None{} : Maybe<&2, U32>},
        true_false(h_kind))
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{_}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.as_f32_kind(val, h_kind):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{raw}:
      Empty.absurd({Ezjson.as_f32(V.JNum{raw}) == None{} : Maybe<&2, F32>},
        true_false(h_kind))
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{_}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.num_keeps(txt, h_ok):
  ok = Equal.sym(Bool, V.num.ok(txt), True{}, h_ok)
  %ok : {V.num.go(txt, _) == V.JNum{txt} : V.Json}
  {==}

def Laws.num_null(txt, h_bad):
  bad = Equal.sym(Bool, V.num.ok(txt), False{}, h_bad)
  %bad : {V.num.go(txt, _) == V.JNull{} : V.Json}
  {==}

def Laws.at_not_arr(val, idx, h_kind):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{its}:
      Empty.absurd({Ezjson.at(V.JArr{its}, idx) == Ezjson.null() : V.Json},
        true_false(h_kind))
    case V.JObj{_}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.get_not_obj(val, key, h_kind):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{ps}:
      Empty.absurd({Ezjson.get(V.JObj{ps}, key) == Ezjson.null() : V.Json},
        true_false(h_kind))
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.as_f32_fits(raw, xx, h_read, h_fin):
  rd = Equal.sym(Maybe<&2, F32>, F32.read(raw), Some{xx}, h_read)
  %rd : {V.f32.fit(_) == Some{xx} : Maybe<&2, F32>}
  fin = Equal.sym(Bool, F32.is_le(F32.abs(xx), 3.4028235e38), True{}, h_fin)
  %fin : {V.f32.fit.go(xx, _) == Some{xx} : Maybe<&2, F32>}
  {==}

def Laws.as_f32_overflow(raw, xx, h_read, h_inf):
  rd = Equal.sym(Maybe<&2, F32>, F32.read(raw), Some{xx}, h_read)
  %rd : {V.f32.fit(_) == None{} : Maybe<&2, F32>}
  inf = Equal.sym(Bool, F32.is_le(F32.abs(xx), 3.4028235e38), False{}, h_inf)
  %inf : {V.f32.fit.go(xx, _) == None{} : Maybe<&2, F32>}
  {==}

def Laws.as_f32_unread(raw, h_read):
  rd = Equal.sym(Maybe<&2, F32>, F32.read(raw), None{}, h_read)
  %rd : {V.f32.fit(_) == None{} : Maybe<&2, F32>}
  {==}

def Laws.has_not_obj(val, key, h_kind):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{ps}:
      Empty.absurd({Ezjson.has(V.JObj{ps}, key) == False{} : Bool},
        true_false(h_kind))
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.has_empty(_key):
  {==}

# a stop that answers true on a match is Bool.or
law stop_or:
  for cond: Bool
  for rest: Bool
  {Lazy.stop(Bool, cond, True{}, _u => rest) == Bool.or(cond, rest) : Bool}

def stop_or(cond, _rest):
  match cond:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.has_first(k2, _vv, ps, key):
  stop_or(V.find.eq(k2, key), V.has.go(V.obj.go(ps), key))

# len.go counts the cells arr.go builds
law len_arr_go:
  for xs: List<&2, V.Json>
  {V.len.go(V.arr.go(xs)) == List.length(&2, V.Json, xs) : Nat}

def len_arr_go(xs):
  match xs:
    case Nil{}:
      {==}
    case hd <> tl:
      %len_arr_go(tl) : {1n+V.len.go(V.arr.go(tl)) == 1n+_ : Nat}
      {==}

# len.go counts the cells obj.go builds
law len_obj_go:
  for ps: List<&1, String & V.Json>
  {V.len.go(V.obj.go(ps)) == List.length(&1, String & V.Json, ps) : Nat}

def len_obj_go(ps):
  match ps:
    case Nil{}:
      {==}
    case (kk, vv) <> tl:
      %len_obj_go(tl) : {1n+V.len.go(V.obj.go(tl)) == 1n+_ : Nat}
      {==}

def Laws.len_arr(xs):
  %len_arr_go(xs) : {U32.from_nat(V.len.go(V.arr.go(xs))) == U32.from_nat(_) : U32}
  {==}

def Laws.len_obj(ps):
  %len_obj_go(ps) : {U32.from_nat(V.len.go(V.obj.go(ps))) == U32.from_nat(_) : U32}
  {==}

def Laws.len_scalar(val, h_arr, h_obj):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{its}:
      Empty.absurd({Ezjson.len(V.JArr{its}) == 0 : U32},
        true_false(h_arr))
    case V.JObj{ps}:
      Empty.absurd({Ezjson.len(V.JObj{ps}) == 0 : U32},
        true_false(h_obj))
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

# Unit for False, Empty for True
def false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law false_true:
  for e: {False{} == True{} : Bool}
  Empty

def false_true(e):
  %e : false_ty(_)
  Unit{}

# both sides of a true and: the left
law and_left:
  for aa: Bool
  for -bb: Bool
  for h_and: {Bool.and(aa, bb) == True{} : Bool}
  {aa == True{} : Bool}

def and_left(aa, _bb, h_and):
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(h_and))

# both sides of a true and: the right
law and_right:
  for aa: Bool
  for -bb: Bool
  for h_and: {Bool.and(aa, bb) == True{} : Bool}
  {bb == True{} : Bool}

def and_right(aa, _bb, h_and):
  match aa:
    case True{}:
      h_and
    case False{}:
      Empty.absurd({_bb == True{} : Bool}, false_true(h_and))

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
      hl = Equal.sym(Bool, V.wf(hd), True{}, and_left(V.wf(hd), Laws.all_wf(tl), h_all))
      %hl : {Lazy.stop(Bool, Bool.not(_), False{}, _u => V.wf.go(V.arr.go(tl), V.WArr{})) == True{} : Bool}
      wf_arr_go(tl, and_right(V.wf(hd), Laws.all_wf(tl), h_all))

def Laws.wf_arr(xs, h_all):
  wf_arr_go(xs, h_all)

# both sides of a true and, from one proof
law and_both:
  for aa: Bool
  for -bb: Bool
  for h_and: {Bool.and(aa, bb) == True{} : Bool}
  ({aa == True{} : Bool} & {bb == True{} : Bool})

def and_both(aa, bb, h_and):
  match aa:
    case True{}:
      ({==}, h_and)
    case False{}:
      Empty.absurd(({False{} == True{} : Bool} & {bb == True{} : Bool}), false_true(h_and))

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
      wf_obj_cons(vv, tl, and_both(V.wf(vv), Laws.all_wf_pairs(tl), h_all), hh => wf_obj_go(tl, hh))

def Laws.wf_obj(ps, h_all):
  wf_obj_go(ps, h_all)

def Laws.print_non_scalar(ch, h_non):
  ok = Equal.sym(Bool, Laws.non_scalar(Char.to_u32(ch)), True{}, h_non)
  %ok : {Print.escape.scalar(Char.to_u32(ch), ch, Bool.not(_))
    == String.from_list([Char.from_u32(65533)]) : String}
  {==}

