# proofs of laws/ItemsGivesElements.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lazy.bend as Lazy
import ../laws/AtIndexesArrays.bend as L1
import ../laws/ItemsGivesElements.bend as Laws
import ../laws/LenCountsItems.bend as L2
import ../laws/defs/ArrayAccess.bend as D1
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/LexemeOrder.bend as M2
import ./lemmas/WordArithmetic.bend as M3

# items.go reads back the cells arr.go builds
law items_go_arr:
  for xs: List<&2, V.Json>
  {V.items.go(V.arr.go(xs)) == xs : List<&2, V.Json>}

def items_go_arr(xs):
  match xs:
    case Nil{}:
      {==}
    case hd <> tl:
      %items_go_arr(tl) : {hd <> V.items.go(V.arr.go(tl)) == hd <> _ : List<&2, V.Json>}
      {==}

def Laws.items_arr(xs):
  items_go_arr(xs)

# a stop whose early answer is False is True only through its rest
law stop_rest:
  for cc: Bool
  for -rr: Bool
  for h_st: {Lazy.stop(Bool, cc, False{}, _u => rr) == True{} : Bool}
  {rr == True{} : Bool}

def stop_rest(cc, _rr, h_st):
  match cc:
    case True{}:
      Empty.absurd({_rr == True{} : Bool}, M2.false_true(h_st))
    case False{}:
      h_st

# arr.go rebuilds a well-formed chain of array cells from its items
law arr_items_go:
  for +cells: V.Json
  for +h_wf: {V.wf.go(cells, V.WArr{}) == True{} : Bool}
  {V.arr.go(V.items.go(cells)) == cells : V.Json}

def arr_items_go(cells, h_wf):
  match cells:
    case V.JNull{}:
      Empty.absurd({V.arr.go(V.items.go(V.JNull{})) == V.JNull{} : V.Json},
        M2.false_true(h_wf))
    case V.JBool{b0}:
      Empty.absurd({V.arr.go(V.items.go(V.JBool{b0})) == V.JBool{b0} : V.Json},
        M2.false_true(h_wf))
    case V.JNum{r0}:
      Empty.absurd({V.arr.go(V.items.go(V.JNum{r0})) == V.JNum{r0} : V.Json},
        M2.false_true(h_wf))
    case V.JStr{s0}:
      Empty.absurd({V.arr.go(V.items.go(V.JStr{s0})) == V.JStr{s0} : V.Json},
        M2.false_true(h_wf))
    case V.JArr{c0}:
      Empty.absurd({V.arr.go(V.items.go(V.JArr{c0})) == V.JArr{c0} : V.Json},
        M2.false_true(h_wf))
    case V.JObj{p0}:
      Empty.absurd({V.arr.go(V.items.go(V.JObj{p0})) == V.JObj{p0} : V.Json},
        M2.false_true(h_wf))
    case V.JNil{}:
      {==}
    case V.JCons{hd, tl}:
      rest = stop_rest(Bool.not(V.wf.go(hd, V.WVal{})), V.wf.go(tl, V.WArr{}), h_wf)
      Equal.cong(V.Json, V.Json, xx => V.JCons{hd, xx}, V.arr.go(V.items.go(tl)), tl,
        arr_items_go(tl, rest))
    case V.JPair{k0, v0, r0}:
      Empty.absurd({V.arr.go(V.items.go(V.JPair{k0, v0, r0})) == V.JPair{k0, v0, r0} : V.Json},
        M2.false_true(h_wf))
    case V.JSpan{s0, n0}:
      Empty.absurd({V.arr.go(V.items.go(V.JSpan{s0, n0})) == V.JSpan{s0, n0} : V.Json},
        M2.false_true(h_wf))
    case V.JBind{s0, n0, v0, r0}:
      Empty.absurd({V.arr.go(V.items.go(V.JBind{s0, n0, v0, r0})) == V.JBind{s0, n0, v0, r0} : V.Json},
        M2.false_true(h_wf))

def Laws.items_back(val, h_wf, h_arr):
  match val:
    case V.JNull{}:
      Empty.absurd({Ezjson.arr(Ezjson.items(V.JNull{})) == V.JNull{} : V.Json},
        M2.false_true(h_arr))
    case V.JBool{b0}:
      Empty.absurd({Ezjson.arr(Ezjson.items(V.JBool{b0})) == V.JBool{b0} : V.Json},
        M2.false_true(h_arr))
    case V.JNum{r0}:
      Empty.absurd({Ezjson.arr(Ezjson.items(V.JNum{r0})) == V.JNum{r0} : V.Json},
        M2.false_true(h_arr))
    case V.JStr{s0}:
      Empty.absurd({Ezjson.arr(Ezjson.items(V.JStr{s0})) == V.JStr{s0} : V.Json},
        M2.false_true(h_arr))
    case V.JArr{cells}:
      Equal.cong(V.Json, V.Json, xx => V.JArr{xx}, V.arr.go(V.items.go(cells)), cells,
        arr_items_go(cells, h_wf))
    case V.JObj{p0}:
      Empty.absurd({Ezjson.arr(Ezjson.items(V.JObj{p0})) == V.JObj{p0} : V.Json},
        M2.false_true(h_arr))
    case V.JNil{}:
      Empty.absurd({Ezjson.arr(Ezjson.items(V.JNil{})) == V.JNil{} : V.Json},
        M2.false_true(h_arr))
    case V.JCons{h0, t0}:
      Empty.absurd({Ezjson.arr(Ezjson.items(V.JCons{h0, t0})) == V.JCons{h0, t0} : V.Json},
        M2.false_true(h_arr))
    case V.JPair{k0, v0, r0}:
      Empty.absurd({Ezjson.arr(Ezjson.items(V.JPair{k0, v0, r0})) == V.JPair{k0, v0, r0} : V.Json},
        M2.false_true(h_arr))
    case V.JSpan{s0, n0}:
      Empty.absurd({Ezjson.arr(Ezjson.items(V.JSpan{s0, n0})) == V.JSpan{s0, n0} : V.Json},
        M2.false_true(h_arr))
    case V.JBind{s0, n0, v0, r0}:
      Empty.absurd({Ezjson.arr(Ezjson.items(V.JBind{s0, n0, v0, r0})) == V.JBind{s0, n0, v0, r0} : V.Json},
        M2.false_true(h_arr))

def Laws.items_len(val, h_wf, h_arr):
  %Laws.items_back(val, h_wf, h_arr) : {Ezjson.len(_)
    == U32.from_nat(List.length(&2, V.Json, Ezjson.items(val))) : U32}
  L2.len_arr(Ezjson.items(val))

def Laws.items_not_arr(val, h_kind):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{cells}:
      Empty.absurd({Ezjson.items(V.JArr{cells}) == [] : List<&2, V.Json>},
        M1.true_false(h_kind))
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

def Laws.items_at(val, idx, h_wf, h_arr):
  %Laws.items_back(val, h_wf, h_arr) : {Ezjson.at(_, idx)
    == D1.nth(Ezjson.items(val), U32.to_nat(idx)) : V.Json}
  L1.at_arr(Ezjson.items(val), idx)
