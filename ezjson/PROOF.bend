# ezjson: the proofs. `bend ezjson/PROOF.bend` is the gate.
import Base
import ./value.bend as V
import ./main.bend as Ezjson
import ./lazy.bend as Lazy
import ./lex.bend as Lex
import ./print.bend as Print
import ./pull.bend as Pull
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

# a U32 that is not k compares unequal to it, once the answer is named
law neq_at:
  for +cp: U32
  for +kk: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, kk) == bb : Bool}
  for contra: {cp == kk : U32} -> Empty
  {U32.is_eq(cp, kk) == False{} : Bool}

def neq_at(cp, kk, bb, eb, contra):
  match bb:
    case False{}:
      eb
    case True{}:
      Empty.absurd({U32.is_eq(cp, kk) == False{} : Bool}, contra(ueq(cp, kk, eb)))

# a code point of U+0020 or more is none of the controls
law ctl_clash:
  for +uu: U32
  for kk: U32
  for h_kk: {U32.is_lt(kk, 32) == True{} : Bool}
  for h_ctl: {U32.is_lt(uu, 32) == False{} : Bool}
  for ee: {uu == kk : U32}
  Empty

def ctl_clash(uu, kk, h_kk, h_ctl, ee):
  lt = Equal.cong(U32, Bool, xx => U32.is_lt(xx, 32), uu, kk, ee)
  true_false(Equal.trans(Bool, True{}, U32.is_lt(uu, 32), False{},
    Equal.trans(Bool, True{}, U32.is_lt(kk, 32), U32.is_lt(uu, 32), Equal.sym(Bool, U32.is_lt(kk, 32), True{}, h_kk),
      Equal.sym(Bool, U32.is_lt(uu, 32), U32.is_lt(kk, 32), lt)), h_ctl))

# a character that differs from Chr{kk} has a different code
law chr_clash:
  for +uu: U32
  for kk: U32
  for h_ne: {Chr{uu} != Chr{kk} : Char}
  for ee: {uu == kk : U32}
  Empty

def chr_clash(uu, kk, h_ne, ee):
  h_ne(Equal.cong(U32, Char, xx => Chr{xx}, uu, kk, ee))

def Laws.esc_quote(ch, h_eq):
  ec = Equal.sym(Char, ch, '"', h_eq)
  %ec : {Print.escape.char(_) == "\\\"" : String}
  {==}

def Laws.esc_backslash(ch, h_eq):
  ec = Equal.sym(Char, ch, '\\', h_eq)
  %ec : {Print.escape.char(_) == "\\\\" : String}
  {==}

def Laws.esc_b(ch, h_eq):
  ec = Equal.sym(Char, ch, '\u{8}', h_eq)
  %ec : {Print.escape.char(_) == "\\b" : String}
  {==}

def Laws.esc_f(ch, h_eq):
  ec = Equal.sym(Char, ch, '\u{c}', h_eq)
  %ec : {Print.escape.char(_) == "\\f" : String}
  {==}

def Laws.esc_n(ch, h_eq):
  ec = Equal.sym(Char, ch, '\n', h_eq)
  %ec : {Print.escape.char(_) == "\\n" : String}
  {==}

def Laws.esc_r(ch, h_eq):
  ec = Equal.sym(Char, ch, '\r', h_eq)
  %ec : {Print.escape.char(_) == "\\r" : String}
  {==}

def Laws.esc_t(ch, h_eq):
  ec = Equal.sym(Char, ch, '\t', h_eq)
  %ec : {Print.escape.char(_) == "\\t" : String}
  {==}

def Laws.esc_plain(ch, h_scalar, h_ctl, h_quote, h_back):
  match ch:
    case Chr{+u}:
      sc = Equal.sym(Bool, Laws.non_scalar(u), False{}, h_scalar)
      %sc : {Print.escape.scalar(u, Chr{u}, Bool.not(_)) == String.from_list([Chr{u}]) : String}
      n34 = Equal.sym(Bool, U32.is_eq(u, 34), False{},
        neq_at(u, 34, U32.is_eq(u, 34), {==}, cc => chr_clash(u, 34, h_quote, cc)))
      %n34 : {Bool.pick(String, _, "\\\"",
        Bool.pick(String, U32.is_eq(u, 92), "\\\\",
          Bool.pick(String, U32.is_eq(u, 8), "\\b",
            Bool.pick(String, U32.is_eq(u, 12), "\\f",
              Bool.pick(String, U32.is_eq(u, 10), "\\n",
                Bool.pick(String, U32.is_eq(u, 13), "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n92 = Equal.sym(Bool, U32.is_eq(u, 92), False{},
        neq_at(u, 92, U32.is_eq(u, 92), {==}, cc => chr_clash(u, 92, h_back, cc)))
      %n92 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, _, "\\\\",
          Bool.pick(String, U32.is_eq(u, 8), "\\b",
            Bool.pick(String, U32.is_eq(u, 12), "\\f",
              Bool.pick(String, U32.is_eq(u, 10), "\\n",
                Bool.pick(String, U32.is_eq(u, 13), "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n8 = Equal.sym(Bool, U32.is_eq(u, 8), False{},
        neq_at(u, 8, U32.is_eq(u, 8), {==}, cc => ctl_clash(u, 8, {==}, h_ctl, cc)))
      %n8 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, False{}, "\\\\",
          Bool.pick(String, _, "\\b",
            Bool.pick(String, U32.is_eq(u, 12), "\\f",
              Bool.pick(String, U32.is_eq(u, 10), "\\n",
                Bool.pick(String, U32.is_eq(u, 13), "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n12 = Equal.sym(Bool, U32.is_eq(u, 12), False{},
        neq_at(u, 12, U32.is_eq(u, 12), {==}, cc => ctl_clash(u, 12, {==}, h_ctl, cc)))
      %n12 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, False{}, "\\\\",
          Bool.pick(String, False{}, "\\b",
            Bool.pick(String, _, "\\f",
              Bool.pick(String, U32.is_eq(u, 10), "\\n",
                Bool.pick(String, U32.is_eq(u, 13), "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n10 = Equal.sym(Bool, U32.is_eq(u, 10), False{},
        neq_at(u, 10, U32.is_eq(u, 10), {==}, cc => ctl_clash(u, 10, {==}, h_ctl, cc)))
      %n10 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, False{}, "\\\\",
          Bool.pick(String, False{}, "\\b",
            Bool.pick(String, False{}, "\\f",
              Bool.pick(String, _, "\\n",
                Bool.pick(String, U32.is_eq(u, 13), "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n13 = Equal.sym(Bool, U32.is_eq(u, 13), False{},
        neq_at(u, 13, U32.is_eq(u, 13), {==}, cc => ctl_clash(u, 13, {==}, h_ctl, cc)))
      %n13 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, False{}, "\\\\",
          Bool.pick(String, False{}, "\\b",
            Bool.pick(String, False{}, "\\f",
              Bool.pick(String, False{}, "\\n",
                Bool.pick(String, _, "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n9 = Equal.sym(Bool, U32.is_eq(u, 9), False{},
        neq_at(u, 9, U32.is_eq(u, 9), {==}, cc => ctl_clash(u, 9, {==}, h_ctl, cc)))
      %n9 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, False{}, "\\\\",
          Bool.pick(String, False{}, "\\b",
            Bool.pick(String, False{}, "\\f",
              Bool.pick(String, False{}, "\\n",
                Bool.pick(String, False{}, "\\r",
                  Bool.pick(String, _, "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      ct = Equal.sym(Bool, U32.is_lt(u, 32), False{}, h_ctl)
      %ct : {Print.escape.rest.go(u, Chr{u}, _) == String.from_list([Chr{u}]) : String}
      {==}

# span.str of no characters, whatever the count
law span_take.nil:
  for +nn: U32
  for bz: Bool
  {V.span.str(SNil{}, nn, bz) == Laws.take(SNil{}, U32.to_nat(nn)) : String}

def span_take.nil(_nn, bz):
  match bz:
    case True{}:
      {==}
    case False{}:
      {==}

# span.str of a character and the rest, once the zero test's answer is named
law span_take.cons:
  for +hd: Char
  for +tl: String
  for +nn: U32
  for bz: Bool
  for ez: {U32.is_zero(nn) == bz : Bool}
  for ih: {V.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))
    == Laws.take(tl, U32.to_nat(U32.sub(nn, 1))) : String}
  {V.span.str(SCon{hd, tl}, nn, bz) == Laws.take(SCon{hd, tl}, U32.to_nat(nn)) : String}

def span_take.cons(hd, tl, nn, bz, ez, ih):
  match bz:
    case True{}:
      e0 = Equal.sym(U32, nn, 0, ueq(nn, 0, ez))
      %e0 : {V.span.str(SCon{hd, tl}, nn, True{}) == Laws.take(SCon{hd, tl}, U32.to_nat(_)) : String}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(nn), 1n+U32.to_nat(U32.sub(nn, 1)), u32_dec(nn, ez))
      %en : {SCon{hd, V.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))}
        == Laws.take(SCon{hd, tl}, _) : String}
      Equal.cong(String, String, xx => SCon{hd, xx}, V.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))),
        Laws.take(tl, U32.to_nat(U32.sub(nn, 1))), ih)

# a span's characters are the first nn characters of its source
law span_take:
  for +src: String
  for +nn: U32
  {V.span.str(src, nn, U32.is_zero(nn)) == Laws.take(src, U32.to_nat(nn)) : String}

def span_take(src, nn):
  match src:
    case SNil{}:
      span_take.nil(nn, U32.is_zero(nn))
    case SCon{hd, tl}:
      span_take.cons(hd, tl, nn, U32.is_zero(nn), {==}, span_take(tl, U32.sub(nn, 1)))

# Some of a span's characters is Some of the first nn characters of its source
law some_span:
  for +src: String
  for +nn: U32
  {Some{V.span.str(src, nn, U32.is_zero(nn))} == Some{Laws.take(src, U32.to_nat(nn))} : Maybe<&2, String>}

def some_span(src, nn):
  Equal.cong(String, Maybe<&2, String>, xx => Some{xx}, V.span.str(src, nn, U32.is_zero(nn)),
    Laws.take(src, U32.to_nat(nn)), span_take(src, nn))

def Laws.text_str(_body):
  {==}

def Laws.text_key(_body):
  {==}

def Laws.text_str_span(src, nn):
  some_span(src, nn)

def Laws.text_key_span(src, nn):
  some_span(src, nn)

def Laws.text_num(src, nn):
  some_span(src, nn)

def Laws.text_none(ev, h_kind):
  match ev:
    case Pull.ENull{}:
      {==}
    case Pull.EBool{_}:
      {==}
    case Pull.ENum{aa, bb}:
      Empty.absurd({Ezjson.text(Pull.ENum{aa, bb}) == None{} : Maybe<&2, String>}, true_false(h_kind))
    case Pull.EStr{aa}:
      Empty.absurd({Ezjson.text(Pull.EStr{aa}) == None{} : Maybe<&2, String>}, true_false(h_kind))
    case Pull.EStrS{aa, bb}:
      Empty.absurd({Ezjson.text(Pull.EStrS{aa, bb}) == None{} : Maybe<&2, String>}, true_false(h_kind))
    case Pull.EKey{aa}:
      Empty.absurd({Ezjson.text(Pull.EKey{aa}) == None{} : Maybe<&2, String>}, true_false(h_kind))
    case Pull.EKeyS{aa, bb}:
      Empty.absurd({Ezjson.text(Pull.EKeyS{aa, bb}) == None{} : Maybe<&2, String>}, true_false(h_kind))
    case Pull.EBeginArr{}:
      {==}
    case Pull.EEndArr{}:
      {==}
    case Pull.EBeginObj{}:
      {==}
    case Pull.EEndObj{}:
      {==}
    case Pull.EEnd{}:
      {==}
    case Pull.EErr{}:
      {==}

def Laws.pull_failed_next(_rest, _stack, _done):
  {==}

def Laws.pull_failed_skip(_rest, _stack, done):
  match done:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.pull_over_skip(_rest, _stack, bad):
  match bad:
    case True{}:
      {==}
    case False{}:
      {==}

# use_err, once the step's stop is in hand
law use_err.at:
  for stop: Pull.Stop
  for cc: Pull.Cur
  for h_err: {Laws.is_err(Laws.ev_of(Pull.next.use((stop, cc)))) == True{} : Bool}
  {Laws.failed(Laws.cur_of(Pull.next.use((stop, cc)))) == True{} : Bool}

def use_err.at(stop, cc, h_err):
  match stop:
    case Pull.SSkip{}:
      {==}
    case Pull.SEv{Pull.ENull{}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.ENull{}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.EBool{aa}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EBool{aa}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.ENum{aa, bb}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.ENum{aa, bb}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.EStr{aa}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EStr{aa}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.EStrS{aa, bb}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EStrS{aa, bb}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.EKey{aa}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EKey{aa}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.EKeyS{aa, bb}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EKeyS{aa, bb}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.EBeginArr{}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EBeginArr{}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.EEndArr{}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EEndArr{}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.EBeginObj{}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EBeginObj{}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.EEndObj{}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EEndObj{}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.EEnd{}}:
      Empty.absurd({Laws.failed(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EEnd{}}, cc)))) == True{} : Bool},
        false_true(h_err))
    case Pull.SEv{Pull.EErr{}}:
      {==}


# an error from a step comes with the failed cursor
law use_err:
  for got: (Pull.Stop & Pull.Cur)
  for h_err: {Laws.is_err(Laws.ev_of(Pull.next.use(got))) == True{} : Bool}
  {Laws.failed(Laws.cur_of(Pull.next.use(got))) == True{} : Bool}

def use_err(got, h_err):
  (stop, cc) = got
  use_err.at(stop, cc, h_err)

# an end from a step comes with an ended cursor, once the stop is in hand
law use_end.at:
  for stop: Pull.Stop
  for cc: Pull.Cur
  for h_end: {Laws.is_end(Laws.ev_of(Pull.next.use((stop, cc)))) == True{} : Bool}
  {Laws.ended(Laws.cur_of(Pull.next.use((stop, cc)))) == True{} : Bool}

def use_end.at(stop, cc, h_end):
  match stop:
    case Pull.SSkip{}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SSkip{}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.ENull{}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.ENull{}}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.EBool{aa}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EBool{aa}}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.ENum{aa, bb}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.ENum{aa, bb}}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.EStr{aa}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EStr{aa}}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.EStrS{aa, bb}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EStrS{aa, bb}}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.EKey{aa}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EKey{aa}}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.EKeyS{aa, bb}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EKeyS{aa, bb}}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.EBeginArr{}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EBeginArr{}}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.EEndArr{}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EEndArr{}}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.EBeginObj{}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EBeginObj{}}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.EEndObj{}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EEndObj{}}, cc)))) == True{} : Bool},
        false_true(h_end))
    case Pull.SEv{Pull.EEnd{}}:
      match cc:
        case Pull.Cur{_, _, _, _}:
          {==}
    case Pull.SEv{Pull.EErr{}}:
      Empty.absurd({Laws.ended(Laws.cur_of(Pull.next.use((Pull.SEv{Pull.EErr{}}, cc)))) == True{} : Bool},
        false_true(h_end))

# an end from a step comes with an ended cursor
law use_end:
  for got: (Pull.Stop & Pull.Cur)
  for h_end: {Laws.is_end(Laws.ev_of(Pull.next.use(got))) == True{} : Bool}
  {Laws.ended(Laws.cur_of(Pull.next.use(got))) == True{} : Bool}

def use_end(got, h_end):
  (stop, cc) = got
  use_end.at(stop, cc, h_end)

def Laws.pull_err_fails(cur, h_err):
  match cur:
    case Pull.Cur{rest, stack, done, bad}:
      match bad:
        case True{}:
          {==}
        case False{}:
          use_err(Pull.next.walk(rest, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}), h_err)

def Laws.pull_end_ends(cur, h_end):
  match cur:
    case Pull.Cur{rest, stack, done, bad}:
      match bad:
        case True{}:
          Empty.absurd({Laws.ended(Laws.cur_of(Ezjson.next(Pull.Cur{rest, stack, done, True{}}))) == True{} : Bool},
            false_true(h_end))
        case False{}:
          use_end(Pull.next.walk(rest, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}), h_end)

def Laws.pull_ended_next(_stack):
  {==}

# whitespace, once whether the code is 13 is known
law ws_d:
  for +uu: U32
  for bb: Bool
  for eb: {U32.is_eq(uu, 13) == bb : Bool}
  for h_ws: {bb == True{} : Bool}
  {Lex.classify(Chr{uu}) == Lex.CSpace{} : Lex.Class}

def ws_d(uu, bb, eb, h_ws):
  match bb:
    case True{}:
      ek = Equal.sym(U32, uu, 13, ueq(uu, 13, eb))
      %ek : {Lex.classify(Chr{_}) == Lex.CSpace{} : Lex.Class}
      {==}
    case False{}:
      Empty.absurd({Lex.classify(Chr{uu}) == Lex.CSpace{} : Lex.Class}, false_true(h_ws))

# whitespace, once whether the code is 10 is known
law ws_c:
  for +uu: U32
  for bb: Bool
  for eb: {U32.is_eq(uu, 10) == bb : Bool}
  for h_ws: {Bool.or(bb, U32.is_eq(uu, 13)) == True{} : Bool}
  {Lex.classify(Chr{uu}) == Lex.CSpace{} : Lex.Class}

def ws_c(uu, bb, eb, h_ws):
  match bb:
    case True{}:
      ek = Equal.sym(U32, uu, 10, ueq(uu, 10, eb))
      %ek : {Lex.classify(Chr{_}) == Lex.CSpace{} : Lex.Class}
      {==}
    case False{}:
      ws_d(uu, U32.is_eq(uu, 13), {==}, h_ws)

# whitespace, once whether the code is 9 is known
law ws_b:
  for +uu: U32
  for bb: Bool
  for eb: {U32.is_eq(uu, 9) == bb : Bool}
  for h_ws: {Bool.or(bb, Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13))) == True{} : Bool}
  {Lex.classify(Chr{uu}) == Lex.CSpace{} : Lex.Class}

def ws_b(uu, bb, eb, h_ws):
  match bb:
    case True{}:
      ek = Equal.sym(U32, uu, 9, ueq(uu, 9, eb))
      %ek : {Lex.classify(Chr{_}) == Lex.CSpace{} : Lex.Class}
      {==}
    case False{}:
      ws_c(uu, U32.is_eq(uu, 10), {==}, h_ws)

# whitespace, once whether the code is 32 is known
law ws_a:
  for +uu: U32
  for bb: Bool
  for eb: {U32.is_eq(uu, 32) == bb : Bool}
  for h_ws: {Bool.or(bb, Bool.or(U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)))) == True{} : Bool}
  {Lex.classify(Chr{uu}) == Lex.CSpace{} : Lex.Class}

def ws_a(uu, bb, eb, h_ws):
  match bb:
    case True{}:
      ek = Equal.sym(U32, uu, 32, ueq(uu, 32, eb))
      %ek : {Lex.classify(Chr{_}) == Lex.CSpace{} : Lex.Class}
      {==}
    case False{}:
      ws_b(uu, U32.is_eq(uu, 9), {==}, h_ws)

# the cursor steps over whitespace between tokens, keeping its state, from
# one character on, the rest given
law go_ws.cons:
  for +ff: Nat
  for +uu: U32
  for +tl: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +goal: Pull.Goal
  for got: ({Laws.is_ws(Chr{uu}) == True{} : Bool} & {Laws.all_ws(tl) == True{} : Bool})
  for ih: {Laws.all_ws(tl) == True{} : Bool}
    -> {Pull.next.go(1n+ff, tl ++ tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}})
      == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}) : Pull.Out}
  {Pull.next.go(1n+ff, SCon{Chr{uu}, tl ++ tail}, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}})
    == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}) : Pull.Out}

def go_ws.cons(ff, uu, tl, tail, stack, goal, got, ih):
  (e1, e2) = got
  cls = Equal.sym(Lex.Class, Lex.classify(Chr{uu}), Lex.CSpace{}, ws_a(uu, U32.is_eq(uu, 32), {==}, e1))
  %cls : {Pull.next.go(1n+ff, tl ++ tail, Pull.look.plan(Chr{uu}, stack, goal, False{}, _))
    == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}) : Pull.Out}
  ih(e2)

# the cursor steps over whitespace between tokens, keeping its state
law go_ws:
  for +ff: Nat
  for +ws: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +goal: Pull.Goal
  for h_ws: {Laws.all_ws(ws) == True{} : Bool}
  {Pull.next.go(1n+ff, ws ++ tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}})
    == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}) : Pull.Out}

def go_ws(ff, ws, tail, stack, goal, h_ws):
  match ws:
    case SNil{}:
      {==}
    case SCon{Chr{+uu}, +tl}:
      go_ws.cons(ff, uu, tl, tail, stack, goal, and_both(Laws.is_ws(Chr{uu}), Laws.all_ws(tl), h_ws),
        hh => go_ws(ff, tl, tail, stack, goal, hh))

# a walk steps over whitespace between tokens, keeping its state
law walk_ws:
  for +ws: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +goal: Pull.Goal
  for h_ws: {Laws.all_ws(ws) == True{} : Bool}
  {Pull.next.walk(ws ++ tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}})
    == Pull.next.walk(tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}) : (Pull.Stop & Pull.Cur)}

def walk_ws(ws, tail, stack, goal, h_ws):
  Equal.cong(Pull.Out, (Pull.Stop & Pull.Cur), xx => Pull.next.fin(Pull.next.grow(32n, 1n, xx)),
    Pull.next.go(4n, ws ++ tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}),
    Pull.next.go(4n, tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}),
    go_ws(3n, ws, tail, stack, goal, h_ws))

# a finished step returns its answer, whatever text is left
law go_done:
  for +ff: Nat
  for +txt: String
  for stop: Pull.Stop
  for saved: String
  for stack: List<&2, Pull.Frame>
  for goal: Pull.Goal
  for done: Bool
  for bad: Bool
  {Pull.next.go(1n+ff, txt, Pull.S{Pull.MDone{stop, saved}, stack, goal, done, bad})
    == Pull.Fin{(stop, Pull.Cur{saved, stack, done, bad})} : Pull.Out}

def go_done(_ff, txt, _stop, _saved, _stack, _goal, _done, _bad):
  match txt:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

def Laws.skip_key(ws, key, fresh, stack, h_ws):
  we = Equal.sym((Pull.Stop & Pull.Cur),
    Pull.next.walk(ws ++ SCon{'"', key},
      Pull.S{Pull.MIdle{}, Pull.FObj{Pull.SKey{}, fresh} <> stack, Pull.GSkip{0n}, False{}, False{}}),
    Pull.next.walk(SCon{'"', key},
      Pull.S{Pull.MIdle{}, Pull.FObj{Pull.SKey{}, fresh} <> stack, Pull.GSkip{0n}, False{}, False{}}),
    walk_ws(ws, SCon{'"', key}, Pull.FObj{Pull.SKey{}, fresh} <> stack, Pull.GSkip{0n}, h_ws))
  %we : {Pull.skip.use(_) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  gd = Equal.sym(Pull.Out, Pull.next.go(4n, key, Pull.err.st(Pull.GSkip{0n})),
    Pull.Fin{(Pull.SEv{Pull.EErr{}}, Pull.Cur{"", [], False{}, True{}})},
    go_done(3n, key, Pull.SEv{Pull.EErr{}}, "", [], Pull.GSkip{0n}, False{}, True{}))
  %gd : {Pull.skip.use(Pull.next.fin(Pull.next.grow(32n, 1n, _))) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  {==}

# the parent after a close, in a top-level skip, is a failure
law close_out_err:
  for ev: Pull.Ev
  for frames: List<&2, Pull.Frame>
  {Pull.close.out(ev, frames, Pull.GSkip{0n}) == Pull.err.st(Pull.GSkip{0n}) : Pull.St}

def close_out_err(_ev, frames):
  match frames:
    case Nil{}:
      {==}
    case Pull.FArr{Pull.SVal{}, _} <> _:
      {==}
    case Pull.FArr{Pull.SCom{}, _} <> _:
      {==}
    case Pull.FArr{Pull.SKey{}, _} <> _:
      {==}
    case Pull.FArr{Pull.SCol{}, _} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, _} <> _:
      {==}
    case Pull.FObj{Pull.SCom{}, _} <> _:
      {==}
    case Pull.FObj{Pull.SKey{}, _} <> _:
      {==}
    case Pull.FObj{Pull.SCol{}, _} <> _:
      {==}

# a close in a top-level skip is a failure, whatever is open
law close_arr_err:
  for stack: List<&2, Pull.Frame>
  {Pull.close.arr(stack, Pull.GSkip{0n}) == Pull.err.st(Pull.GSkip{0n}) : Pull.St}

def close_arr_err(stack):
  match stack:
    case Nil{}:
      {==}
    case Pull.FArr{Pull.SVal{}, True{}} <> frames:
      close_out_err(Pull.EEndArr{}, frames)
    case Pull.FArr{Pull.SVal{}, False{}} <> _:
      {==}
    case Pull.FArr{Pull.SCom{}, True{}} <> frames:
      close_out_err(Pull.EEndArr{}, frames)
    case Pull.FArr{Pull.SCom{}, False{}} <> frames:
      close_out_err(Pull.EEndArr{}, frames)
    case Pull.FArr{Pull.SKey{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SKey{}, False{}} <> _:
      {==}
    case Pull.FArr{Pull.SCol{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SCol{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SCom{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SCom{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SKey{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SKey{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SCol{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SCol{}, False{}} <> _:
      {==}

def Laws.skip_close_arr(ws, rest, stack, h_ws):
  we = Equal.sym((Pull.Stop & Pull.Cur),
    Pull.next.walk(ws ++ SCon{']', rest}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{}, False{}}),
    Pull.next.walk(SCon{']', rest}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{}, False{}}),
    walk_ws(ws, SCon{']', rest}, stack, Pull.GSkip{0n}, h_ws))
  %we : {Pull.skip.use(_) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  ce = Equal.sym(Pull.St, Pull.close.arr(stack, Pull.GSkip{0n}), Pull.err.st(Pull.GSkip{0n}), close_arr_err(stack))
  %ce : {Pull.skip.use(Pull.next.fin(Pull.next.grow(32n, 1n, Pull.next.go(4n, rest, _))))
    == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  gd = Equal.sym(Pull.Out, Pull.next.go(4n, rest, Pull.err.st(Pull.GSkip{0n})),
    Pull.Fin{(Pull.SEv{Pull.EErr{}}, Pull.Cur{"", [], False{}, True{}})},
    go_done(3n, rest, Pull.SEv{Pull.EErr{}}, "", [], Pull.GSkip{0n}, False{}, True{}))
  %gd : {Pull.skip.use(Pull.next.fin(Pull.next.grow(32n, 1n, _))) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  {==}

# a close in a top-level skip is a failure, whatever is open
law close_obj_err:
  for stack: List<&2, Pull.Frame>
  {Pull.close.obj(stack, Pull.GSkip{0n}) == Pull.err.st(Pull.GSkip{0n}) : Pull.St}

def close_obj_err(stack):
  match stack:
    case Nil{}:
      {==}
    case Pull.FArr{Pull.SVal{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SVal{}, False{}} <> _:
      {==}
    case Pull.FArr{Pull.SCom{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SCom{}, False{}} <> _:
      {==}
    case Pull.FArr{Pull.SKey{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SKey{}, False{}} <> _:
      {==}
    case Pull.FArr{Pull.SCol{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SCol{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SCom{}, True{}} <> frames:
      close_out_err(Pull.EEndObj{}, frames)
    case Pull.FObj{Pull.SCom{}, False{}} <> frames:
      close_out_err(Pull.EEndObj{}, frames)
    case Pull.FObj{Pull.SKey{}, True{}} <> frames:
      close_out_err(Pull.EEndObj{}, frames)
    case Pull.FObj{Pull.SKey{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SCol{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SCol{}, False{}} <> _:
      {==}

def Laws.skip_close_obj(ws, rest, stack, h_ws):
  we = Equal.sym((Pull.Stop & Pull.Cur),
    Pull.next.walk(ws ++ SCon{'}', rest}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{}, False{}}),
    Pull.next.walk(SCon{'}', rest}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{}, False{}}),
    walk_ws(ws, SCon{'}', rest}, stack, Pull.GSkip{0n}, h_ws))
  %we : {Pull.skip.use(_) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  ce = Equal.sym(Pull.St, Pull.close.obj(stack, Pull.GSkip{0n}), Pull.err.st(Pull.GSkip{0n}), close_obj_err(stack))
  %ce : {Pull.skip.use(Pull.next.fin(Pull.next.grow(32n, 1n, Pull.next.go(4n, rest, _))))
    == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  gd = Equal.sym(Pull.Out, Pull.next.go(4n, rest, Pull.err.st(Pull.GSkip{0n})),
    Pull.Fin{(Pull.SEv{Pull.EErr{}}, Pull.Cur{"", [], False{}, True{}})},
    go_done(3n, rest, Pull.SEv{Pull.EErr{}}, "", [], Pull.GSkip{0n}, False{}, True{}))
  %gd : {Pull.skip.use(Pull.next.fin(Pull.next.grow(32n, 1n, _))) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  {==}

# U32 increment and decrement, bit by bit. Word.adc adds the low bit first;
# with a zero second word it adds or takes away only the carry

# adding the carry then taking it back, from the lowest bit up, is nothing
law adc_inc_dec:
  for +qq: Nat
  for +aw: Word(qq)
  for cc: Bool
  {Word.adc(qq, Word.adc(qq, aw, Word.zero(qq), False{}, cc), Word.zero(qq), True{}, Bool.not(cc)) == aw : Word(qq)}

def adc_inc_dec(qq, aw, cc):
  match qq:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match aw cc:
        case WCon{False{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{True{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{False{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{True{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, True{}), Word.zero(pp), True{}, False{}), at,
            adc_inc_dec(pp, at, True{}))

# taking the carry away then adding it back, from the lowest bit up, is nothing
law adc_dec_inc:
  for +qq: Nat
  for +aw: Word(qq)
  for cc: Bool
  {Word.adc(qq, Word.adc(qq, aw, Word.zero(qq), True{}, cc), Word.zero(qq), False{}, Bool.not(cc)) == aw : Word(qq)}

def adc_dec_inc(qq, aw, cc):
  match qq:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match aw cc:
        case WCon{False{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), True{}, True{}), Word.zero(pp), False{}, False{}), at,
            adc_dec_inc(pp, at, True{}))
        case WCon{True{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), True{}, True{}), Word.zero(pp), False{}, False{}), at,
            adc_dec_inc(pp, at, True{}))
        case WCon{False{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), True{}, False{}), Word.zero(pp), False{}, True{}), at,
            adc_dec_inc(pp, at, False{}))
        case WCon{True{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), True{}, True{}), Word.zero(pp), False{}, False{}), at,
            adc_dec_inc(pp, at, True{}))

# one more then one less is the same U32
law u32_dec_inc:
  for +uu: U32
  {U32.sub(U32.add(uu, 1), 1) == uu : U32}

def u32_dec_inc(uu):
  match uu:
    case U32{WCon{False{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{False{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), False{}, False{}), Word.zero(31n), True{}, True{}), at,
        adc_inc_dec(31n, at, False{}))
    case U32{WCon{True{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{True{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), False{}, True{}), Word.zero(31n), True{}, False{}), at,
        adc_inc_dec(31n, at, True{}))

# one less then one more is the same U32
law u32_inc_dec:
  for +uu: U32
  {U32.add(U32.sub(uu, 1), 1) == uu : U32}

def u32_inc_dec(uu):
  match uu:
    case U32{WCon{False{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{False{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), True{}, False{}), Word.zero(31n), False{}, True{}), at,
        adc_dec_inc(31n, at, False{}))
    case U32{WCon{True{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{True{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), True{}, True{}), Word.zero(31n), False{}, False{}), at,
        adc_dec_inc(31n, at, True{}))

# one more than a U32 below the top is not zero, once the answer is named
law inc_nonzero.at:
  for +uu: U32
  for bb: Bool
  for eb: {U32.is_zero(U32.add(uu, 1)) == bb : Bool}
  for h_top: {U32.is_eq(uu, 4294967295) == False{} : Bool}
  {U32.is_zero(U32.add(uu, 1)) == False{} : Bool}

def inc_nonzero.at(uu, bb, eb, h_top):
  match bb:
    case False{}:
      eb
    case True{}:
      e0 = ueq(U32.add(uu, 1), 0, eb)
      back = Equal.sym(U32, U32.sub(U32.add(uu, 1), 1), uu, u32_dec_inc(uu))
      down = Equal.cong(U32, U32, xx => U32.sub(xx, 1), U32.add(uu, 1), 0, e0)
      at_top = Equal.trans(U32, uu, U32.sub(U32.add(uu, 1), 1), 4294967295, back, down)
      top = Equal.cong(U32, Bool, xx => U32.is_eq(xx, 4294967295), uu, 4294967295, at_top)
      Empty.absurd({U32.is_zero(U32.add(uu, 1)) == False{} : Bool},
        true_false(Equal.trans(Bool, True{}, U32.is_eq(uu, 4294967295), False{},
          Equal.sym(Bool, U32.is_eq(uu, 4294967295), True{}, top), h_top)))

# one more than a U32 below the top is not zero
law inc_nonzero:
  for +uu: U32
  for h_top: {U32.is_eq(uu, 4294967295) == False{} : Bool}
  {U32.is_zero(U32.add(uu, 1)) == False{} : Bool}

def inc_nonzero(uu, h_top):
  inc_nonzero.at(uu, U32.is_zero(U32.add(uu, 1)), {==}, h_top)
