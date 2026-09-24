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

# a bit compares equal to itself
law fin_self:
  for bb: Bool
  {Word.cmp.fin(bb, bb, EQ{}) == EQ{} : Cmp}

def fin_self(bb):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# words compare equal to themselves
law weq_refl:
  for n: Nat
  for +ww: Word(n)
  {Word.cmp(n, ww, ww) == EQ{} : Cmp}

def weq_refl(n, ww):
  match n:
    case 0n:
      {==}
    case 1n+pp:
      match ww:
        case WCon{bb, tt}:
          ih = Equal.sym(Cmp, Word.cmp(pp, tt, tt), EQ{}, weq_refl(pp, tt))
          %ih : {Word.cmp.fin(bb, bb, _) == EQ{} : Cmp}
          fin_self(bb)

# a character compares equal to itself
law char_eq_refl:
  for +ch: Char
  {Char.is_eq(ch, ch) == True{} : Bool}

def char_eq_refl(ch):
  match ch:
    case Chr{U32{ww}}:
      rf = Equal.sym(Cmp, Word.cmp(32n, ww, ww), EQ{}, weq_refl(32n, ww))
      %rf : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# words that compare equal, bit by bit past the first: the rest equal, the
# first bits the same. From bolt's cfg4.weq.arm
law weq.arm:
  for -pp: Nat
  for -at: Word(pp)
  for -bt: Word(pp)
  for cc: Cmp
  for ec: {Word.cmp(pp, at, bt) == cc : Cmp}
  for ih: {Cmp.is_eq(Word.cmp(pp, at, bt)) == True{} : Bool} -> {at == bt : Word(pp)}
  for ab: Bool
  for bb: Bool
  for ee: {Cmp.is_eq(Word.cmp.fin(ab, bb, cc)) == True{} : Bool}
  {WCon{ab, at} == WCon{bb, bt} : Word.Con<pp>}

def weq.arm(pp, at, bt, cc, ec, ih, ab, bb, ee):
  match cc:
    case LT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<pp>}, false_true(ee))
    case GT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<pp>}, false_true(ee))
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww}, at, bt,
            ih(Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(pp, at, bt), EQ{}, ec)))
        case True{} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww}, at, bt,
            ih(Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(pp, at, bt), EQ{}, ec)))
        case False{} True{}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<pp>}, false_true(ee))
        case True{} False{}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<pp>}, false_true(ee))

# words that compare equal are equal. From bolt's cfg4.weq
law weq:
  for n: Nat
  for aw: Word(n)
  for bw: Word(n)
  for ee: {Cmp.is_eq(Word.cmp(n, aw, bw)) == True{} : Bool}
  {aw == bw : Word(n)}

def weq(n, aw, bw, ee):
  match n:
    case 0n:
      match aw bw:
        case WNil{} WNil{}:
          {==}
    case 1n+(+pp):
      match aw bw:
        case WCon{ab, +at} WCon{bb, +bt}:
          weq.arm(pp, at, bt, Word.cmp(pp, at, bt), {==}, xx => weq(pp, at, bt, xx), ab, bb, ee)

# U32s that compare equal are equal. From bolt's cfg4.ueq
law ueq:
  for au: U32
  for bu: U32
  for ee: {U32.is_eq(au, bu) == True{} : Bool}
  {au == bu : U32}

def ueq(au, bu, ee):
  match au bu:
    case U32{xw} U32{yw}:
      Equal.cong(Word(32n), U32, ww => U32{ww}, xw, yw, weq(32n, xw, yw, ee))

# find.eq holds of a string and itself
law find_eq_refl:
  for +txt: String
  {V.find.eq.go(txt, txt, True{}) == True{} : Bool}

def find_eq_refl(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{ch, tl}:
      rf = Equal.sym(Bool, Char.is_eq(ch, ch), True{}, char_eq_refl(ch))
      %rf : {V.find.eq.go(tl, tl, _) == True{} : Bool}
      find_eq_refl(tl)

# two strings whose first characters' codes are equal and whose rests are equal
law find_eq_cons:
  for +xu: U32
  for +yu: U32
  for -xs: String
  for -ys: String
  for got: ({U32.is_eq(xu, yu) == True{} : Bool} & {xs == ys : String})
  {SCon{Chr{xu}, xs} == SCon{Chr{yu}, ys} : String}

def find_eq_cons(xu, yu, xs, ys, got):
  (eu, es) = got
  ex = ueq(xu, yu, eu)
  %ex : {SCon{Chr{xu}, xs} == SCon{Chr{_}, ys} : String}
  %es : {SCon{Chr{xu}, xs} == SCon{Chr{xu}, _} : String}
  {==}

# find.eq holds only of equal strings, and only while the characters so far agreed
law find_eq_sound:
  for +lhs: String
  for +rhs: String
  for same: Bool
  for ee: {V.find.eq.go(lhs, rhs, same) == True{} : Bool}
  ({same == True{} : Bool} & {lhs == rhs : String})

def find_eq_sound(lhs, rhs, same, ee):
  match lhs rhs same:
    case SNil{} SNil{} True{}:
      ({==}, {==})
    case SNil{} SNil{} False{}:
      Empty.absurd(({False{} == True{} : Bool} & {SNil{} == SNil{} : String}), false_true(ee))
    case SNil{} SCon{hh, tt} sm:
      Empty.absurd(({sm == True{} : Bool} & {SNil{} == SCon{hh, tt} : String}), false_true(ee))
    case SCon{hh, tt} SNil{} sm:
      Empty.absurd(({sm == True{} : Bool} & {SCon{hh, tt} == SNil{} : String}), false_true(ee))
    case SCon{Chr{+xu}, +xs} SCon{Chr{+yu}, +ys} True{}:
      ({==}, find_eq_cons(xu, yu, xs, ys, find_eq_sound(xs, ys, U32.is_eq(xu, yu), ee)))
    case SCon{xc, xs} SCon{yc, ys} False{}:
      Empty.absurd(({False{} == True{} : Bool} & {SCon{xc, xs} == SCon{yc, ys} : String}), false_true(ee))


# find.eq holding of two different strings is impossible
law find_eq_clash:
  for -lhs: String
  for -rhs: String
  for got: ({True{} == True{} : Bool} & {lhs == rhs : String})
  for h_ne: {lhs != rhs : String}
  Empty

def find_eq_clash(_lhs, _rhs, got, h_ne):
  (_st, same) = got
  h_ne(same)

# find.eq is false of two different strings, once its answer is named
law find_eq_false.at:
  for +lhs: String
  for +rhs: String
  for bb: Bool
  for eb: {V.find.eq.go(lhs, rhs, True{}) == bb : Bool}
  for h_ne: {lhs != rhs : String}
  {V.find.eq.go(lhs, rhs, True{}) == False{} : Bool}

def find_eq_false.at(lhs, rhs, bb, eb, h_ne):
  match bb:
    case False{}:
      eb
    case True{}:
      Empty.absurd({V.find.eq.go(lhs, rhs, True{}) == False{} : Bool},
        find_eq_clash(lhs, rhs, find_eq_sound(lhs, rhs, True{}, eb), h_ne))

# find.eq is false of two different strings
law find_eq_false:
  for +lhs: String
  for +rhs: String
  for h_ne: {lhs != rhs : String}
  {V.find.eq.go(lhs, rhs, True{}) == False{} : Bool}

def find_eq_false(lhs, rhs, h_ne):
  find_eq_false.at(lhs, rhs, V.find.eq.go(lhs, rhs, True{}), {==}, h_ne)

def Laws.get_empty(_key):
  {==}

# a key that matched: its value, whatever pairs follow
law get_hit.rest:
  for ps: List<&1, String & V.Json>
  for +key: String
  for vv: V.Json
  {V.find.at(V.obj.go(ps), key, True{}, vv) == vv : V.Json}

def get_hit.rest(ps, _key, _vv):
  match ps:
    case Nil{}:
      {==}
    case (_k3, _v3) <> _tl:
      {==}

def Laws.get_hit(k2, vv, ps, key, h_eq):
  ek = Equal.sym(String, k2, key, h_eq)
  %ek : {V.find.at(V.obj.go(ps), key, V.find.eq.go(_, key, True{}), vv) == vv : V.Json}
  rf = Equal.sym(Bool, V.find.eq.go(key, key, True{}), True{}, find_eq_refl(key))
  %rf : {V.find.at(V.obj.go(ps), key, _, vv) == vv : V.Json}
  get_hit.rest(ps, key, vv)

# a key that missed: the rest of the pairs answer, as get on them would
law get_miss.rest:
  for ps: List<&1, String & V.Json>
  for +key: String
  for vv: V.Json
  {V.find.at(V.obj.go(ps), key, False{}, vv) == Ezjson.get(Ezjson.obj(ps), key) : V.Json}

def get_miss.rest(ps, _key, _vv):
  match ps:
    case Nil{}:
      {==}
    case (_k3, _v3) <> _tl:
      {==}

def Laws.get_miss(k2, vv, ps, key, h_ne):
  nf = Equal.sym(Bool, V.find.eq.go(k2, key, True{}), False{}, find_eq_false(k2, key, h_ne))
  %nf : {V.find.at(V.obj.go(ps), key, _, vv) == Ezjson.get(Ezjson.obj(ps), key) : V.Json}
  get_miss.rest(ps, key, vv)

def Laws.has_hit(k2, _vv, ps, key, h_eq):
  ek = Equal.sym(String, k2, key, h_eq)
  %ek : {Lazy.stop(Bool, V.find.eq.go(_, key, True{}), True{}, _u => V.has.go(V.obj.go(ps), key)) == True{} : Bool}
  rf = Equal.sym(Bool, V.find.eq.go(key, key, True{}), True{}, find_eq_refl(key))
  %rf : {Lazy.stop(Bool, _, True{}, _u => V.has.go(V.obj.go(ps), key)) == True{} : Bool}
  {==}

def Laws.has_miss(k2, _vv, ps, key, h_ne):
  nf = Equal.sym(Bool, V.find.eq.go(k2, key, True{}), False{}, find_eq_false(k2, key, h_ne))
  %nf : {Lazy.stop(Bool, _, True{}, _u => V.has.go(V.obj.go(ps), key)) == Ezjson.has(Ezjson.obj(ps), key) : Bool}
  {==}

# RFC 8259 §6: num.ok's states against the grammar. One lemma per state,
# from the last state back to the start; each `_at` lemma takes the answer
# of one character test as a parameter, so it can match on it

# a rejected number stays rejected
law st_bad:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NBad{}) == False{} : Bool}

def st_bad(cs):
  match cs:
    case Nil{}:
      {==}
    case _ch <> tl:
      st_bad(tl)

# exp's last digits: *DIGIT, then the end
law st_expd:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NExpD{}) == Laws.digits_end(cs) : Bool}

# one digit test of an exponent, the rest given
law expd_at:
  for +tl: List<&2, Char>
  for bd: Bool
  for ih: {V.num.ok.go(tl, V.NExpD{}) == Laws.digits_end(tl) : Bool}
  {V.num.ok.go(tl, V.num.ok.step.expd.go(bd)) == Laws.when(bd, Laws.digits_end(tl), False{}) : Bool}

def expd_at(tl, bd, ih):
  match bd:
    case True{}:
      ih
    case False{}:
      st_bad(tl)

def st_expd(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      expd_at(tl, Laws.digit(ch), st_expd(tl))

# exp after its sign: 1*DIGIT, then the end
law st_expn:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NExpN{}) == Laws.digits1_end(cs) : Bool}

def st_expn(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      expd_at(tl, Laws.digit(ch), st_expd(tl))

# after e, not a plus: a minus, or the first digit
law exp_minus_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bm: Bool
  {V.num.ok.go(tl, V.num.ok.step.exps.minus.go(Char.to_u32(ch), bm))
    == Laws.when(bm, Laws.digits1_end(tl), Laws.when(Laws.digit(ch), Laws.digits_end(tl), False{})) : Bool}

def exp_minus_at(ch, tl, bm):
  match bm:
    case True{}:
      st_expn(tl)
    case False{}:
      expd_at(tl, Laws.digit(ch), st_expd(tl))

# after e: a plus, a minus, or the first digit
law exp_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bp: Bool
  {V.num.ok.go(tl, V.num.ok.step.exps.go(Char.to_u32(ch), bp))
    == Laws.when(bp, Laws.digits1_end(tl),
      Laws.when(Laws.is_cp(ch, 45), Laws.digits1_end(tl),
        Laws.when(Laws.digit(ch), Laws.digits_end(tl), False{}))) : Bool}

def exp_at(ch, tl, bp):
  match bp:
    case True{}:
      st_expn(tl)
    case False{}:
      exp_minus_at(ch, tl, Laws.is_cp(ch, 45))

# exp after its e
law st_exp:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NExp{}) == Laws.exp_body(cs) : Bool}

def st_exp(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      exp_at(ch, tl, Laws.is_cp(ch, 43))

# an e starts exp; anything else is not a number
law mark_at:
  for +tl: List<&2, Char>
  for be: Bool
  {V.num.ok.go(tl, V.num.ok.step.mark.go(be)) == Laws.when(be, Laws.exp_body(tl), False{}) : Bool}

def mark_at(tl, be):
  match be:
    case True{}:
      st_exp(tl)
    case False{}:
      st_bad(tl)

# frac's digits after the first, then [ exp ], then the end
law st_frac:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NFrac{}) == Laws.digits_exp_end(cs) : Bool}

# one character of frac's digits, the rest given
law frac_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bd: Bool
  for ih: {V.num.ok.go(tl, V.NFrac{}) == Laws.digits_exp_end(tl) : Bool}
  {V.num.ok.go(tl, V.num.ok.step.frac.go(Char.to_u32(ch), True{}, bd))
    == Laws.when(bd, Laws.digits_exp_end(tl), Laws.when(Laws.is_e(ch), Laws.exp_body(tl), False{})) : Bool}

def frac_at(ch, tl, bd, ih):
  match bd:
    case True{}:
      ih
    case False{}:
      mark_at(tl, Laws.is_e(ch))

def st_frac(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      frac_at(ch, tl, Laws.digit(ch), st_frac(tl))

# frac after its decimal point
law st_dot:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NDot{}) == Laws.frac_body(cs) : Bool}

# the first digit of frac
law dot_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bd: Bool
  {V.num.ok.go(tl, V.num.ok.step.frac.go(Char.to_u32(ch), False{}, bd))
    == Laws.when(bd, Laws.digits_exp_end(tl), False{}) : Bool}

def dot_at(_ch, tl, bd):
  match bd:
    case True{}:
      st_frac(tl)
    case False{}:
      st_bad(tl)

def st_dot(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      dot_at(ch, tl, Laws.digit(ch))

# after int, not a digit: a decimal point, an e, or not a number
law other_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bdot: Bool
  {V.num.ok.go(tl, V.num.ok.step.body.other.go(Char.to_u32(ch), bdot))
    == Laws.when(bdot, Laws.frac_body(tl), Laws.when(Laws.is_e(ch), Laws.exp_body(tl), False{})) : Bool}

def other_at(ch, tl, bdot):
  match bdot:
    case True{}:
      st_dot(tl)
    case False{}:
      mark_at(tl, Laws.is_e(ch))

# after an int of 0
law st_zero:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NZero{}) == Laws.zero_rest(cs) : Bool}

# one character after 0: a digit is not a number
law zero_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bd: Bool
  {V.num.ok.go(tl, V.num.ok.step.body.go(Char.to_u32(ch), False{}, bd))
    == Laws.when(bd, False{},
      Laws.when(Laws.is_cp(ch, 46), Laws.frac_body(tl), Laws.when(Laws.is_e(ch), Laws.exp_body(tl), False{}))) : Bool}

def zero_at(ch, tl, bd):
  match bd:
    case True{}:
      st_bad(tl)
    case False{}:
      other_at(ch, tl, Laws.is_cp(ch, 46))

def st_zero(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      zero_at(ch, tl, Laws.digit(ch))

# after digit1-9 and any digits
law st_dig:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NDig{}) == Laws.digits_rest(cs) : Bool}

# one character after int's digits, the rest given
law dig_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bd: Bool
  for ih: {V.num.ok.go(tl, V.NDig{}) == Laws.digits_rest(tl) : Bool}
  {V.num.ok.go(tl, V.num.ok.step.body.go(Char.to_u32(ch), True{}, bd))
    == Laws.when(bd, Laws.digits_rest(tl),
      Laws.when(Laws.is_cp(ch, 46), Laws.frac_body(tl), Laws.when(Laws.is_e(ch), Laws.exp_body(tl), False{}))) : Bool}

def dig_at(ch, tl, bd, ih):
  match bd:
    case True{}:
      ih
    case False{}:
      other_at(ch, tl, Laws.is_cp(ch, 46))

def st_dig(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      dig_at(ch, tl, Laws.digit(ch), st_dig(tl))

# int's first character, not 0: digit1-9 or not a number
law lead_at:
  for +tl: List<&2, Char>
  for bl: Bool
  {V.num.ok.go(tl, V.num.ok.step.lead(bl)) == Laws.when(bl, Laws.digits_rest(tl), False{}) : Bool}

def lead_at(tl, bl):
  match bl:
    case True{}:
      st_dig(tl)
    case False{}:
      st_bad(tl)

# int's first character
law int_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bz: Bool
  {V.num.ok.go(tl, V.num.ok.step.int.go(Char.to_u32(ch), bz))
    == Laws.when(bz, Laws.zero_rest(tl), Laws.when(Laws.digit19(ch), Laws.digits_rest(tl), False{})) : Bool}

def int_at(ch, tl, bz):
  match bz:
    case True{}:
      st_zero(tl)
    case False{}:
      lead_at(tl, Laws.digit19(ch))

# int [ frac ] [ exp ]
law st_int:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NInt{}) == Laws.int_end(cs) : Bool}

def st_int(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      int_at(ch, tl, Laws.is_cp(ch, 48))

# the first character: minus, or int's first
law start_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bm: Bool
  {V.num.ok.go(tl, V.num.ok.step.start.go(Char.to_u32(ch), bm))
    == Laws.when(bm, Laws.int_end(tl), Laws.int_end(ch <> tl)) : Bool}

def start_at(ch, tl, bm):
  match bm:
    case True{}:
      st_int(tl)
    case False{}:
      st_int(ch <> tl)

# the whole number
law st_start:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NStart{}) == Laws.number(cs) : Bool}

def st_start(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      start_at(ch, tl, Laws.is_cp(ch, 45))

def Laws.num_grammar(txt):
  st_start(String.to_list(txt))

# one bit of adc_zero_carry, the rest given
law adc_zero_carry.at:
  for +qq: Nat
  for ab: Bool
  for -at: Word(qq)
  for ih: {Word.adc(qq, at, Word.zero(qq), True{}, True{}) == at : Word(qq)}
  {Word.adc.con(qq, at, Word.zero(qq), True{}, Bool.full_add(ab, True{}, True{})) == WCon{ab, at} : Word.Con<qq>}

def adc_zero_carry.at(qq, ab, at, ih):
  match ab:
    case True{}:
      Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww},
        Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, ih)
    case False{}:
      Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww},
        Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, ih)

# subtracting zero with the carry in adds nothing: a - 0 - 1 + 1 is a
law adc_zero_carry:
  for +pp: Nat
  for +aw: Word(pp)
  {Word.adc(pp, aw, Word.zero(pp), True{}, True{}) == aw : Word(pp)}

def adc_zero_carry(pp, aw):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+(+qq):
      match aw:
        case WCon{ab, +at}:
          adc_zero_carry.at(qq, ab, at, adc_zero_carry(qq, at))

# a word whose first bit is clear and that is not zero: the rest is not zero
law fin_ff:
  for cc: Cmp
  for h_nz: {Cmp.is_eq(Word.cmp.fin(False{}, False{}, cc)) == False{} : Bool}
  {Cmp.is_eq(cc) == False{} : Bool}

def fin_ff(cc, h_nz):
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, true_false(h_nz))
    case GT{}:
      {==}

# subtracting zero with no carry in takes one: a - 0 - 1, one less than a
# when a is not zero
law adc_zero_borrow:
  for +pp: Nat
  for +aw: Word(pp)
  for h_nz: {Cmp.is_eq(Word.cmp(pp, aw, Word.zero(pp))) == False{} : Bool}
  {1n+Word.to_nat(pp, Word.adc(pp, aw, Word.zero(pp), True{}, False{})) == Word.to_nat(pp, aw) : Nat}

def adc_zero_borrow(pp, aw, h_nz):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          Empty.absurd({1n == 0n : Nat}, true_false(h_nz))
    case 1n+(+qq):
      match aw:
        case WCon{True{}, +at}:
          lc = Equal.sym(Word(qq), Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, adc_zero_carry(qq, at))
          %lc : {1n+Nat.double(Word.to_nat(qq, _)) == 1n+Nat.double(Word.to_nat(qq, at)) : Nat}
          {==}
        case WCon{False{}, +at}:
          ih = adc_zero_borrow(qq, at, fin_ff(Word.cmp(qq, at, Word.zero(qq)), h_nz))
          %ih : {2n+Nat.double(Word.to_nat(qq, Word.adc(qq, at, Word.zero(qq), True{}, False{})))
            == Nat.double(_) : Nat}
          {==}

# one less than a nonzero U32, as a Nat
law u32_dec:
  for +uu: U32
  for h_nz: {U32.is_zero(uu) == False{} : Bool}
  {U32.to_nat(uu) == 1n+U32.to_nat(U32.sub(uu, 1)) : Nat}

def u32_dec(uu, h_nz):
  match uu:
    case U32{WCon{True{}, +at}}:
      lc = Equal.sym(Word(31n), Word.adc(31n, at, Word.zero(31n), True{}, True{}), at, adc_zero_carry(31n, at))
      %lc : {1n+Nat.double(Word.to_nat(31n, at)) == 1n+Nat.double(Word.to_nat(31n, _)) : Nat}
      {==}
    case U32{WCon{False{}, +at}}:
      ih = adc_zero_borrow(31n, at, fin_ff(Word.cmp(31n, at, Word.zero(31n)), h_nz))
      %ih : {Nat.double(_)
        == 2n+Nat.double(Word.to_nat(31n, Word.adc(31n, at, Word.zero(31n), True{}, False{}))) : Nat}
      {==}

# one cell of at.go, once whether the index is zero is known
law at_step:
  for +hd: V.Json
  for +tl: List<&2, V.Json>
  for +idx: U32
  for bz: Bool
  for ez: {U32.is_zero(idx) == bz : Bool}
  for ih: {V.at.go(V.arr.go(tl), U32.sub(idx, 1)) == Laws.nth(tl, U32.to_nat(U32.sub(idx, 1))) : V.Json}
  {Lazy.stop(V.Json, bz, hd, _u => V.at.go(V.arr.go(tl), U32.sub(idx, 1)))
    == Laws.nth(hd <> tl, U32.to_nat(idx)) : V.Json}

def at_step(hd, tl, idx, bz, ez, ih):
  match bz:
    case True{}:
      e0 = Equal.sym(U32, idx, 0, ueq(idx, 0, ez))
      %e0 : {hd == Laws.nth(hd <> tl, U32.to_nat(_)) : V.Json}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(idx), 1n+U32.to_nat(U32.sub(idx, 1)), u32_dec(idx, ez))
      %en : {V.at.go(V.arr.go(tl), U32.sub(idx, 1)) == Laws.nth(hd <> tl, _) : V.Json}
      ih

# at.go over the cells arr.go builds is nth at the index
law at_go_nth:
  for +xs: List<&2, V.Json>
  for +idx: U32
  {V.at.go(V.arr.go(xs), idx) == Laws.nth(xs, U32.to_nat(idx)) : V.Json}

def at_go_nth(xs, idx):
  match xs:
    case Nil{}:
      {==}
    case hd <> tl:
      at_step(hd, tl, idx, U32.is_zero(idx), {==}, at_go_nth(tl, U32.sub(idx, 1)))

def Laws.at_arr(xs, idx):
  at_go_nth(xs, idx)

