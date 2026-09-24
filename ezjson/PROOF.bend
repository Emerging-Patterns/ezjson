# ezjson: the proofs. `bend ezjson/PROOF.bend` is the gate.
import Base
import ./value.bend as V
import ./main.bend as Ezjson
import ./lazy.bend as Lazy
import ./lex.bend as Lex
import ./parse.bend as Parse
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

# what is left of `src` after its first `nn` characters, counted as span.str
# counts them
def sdrop(src: String, +nn: U32, zero: Bool) -> String:
  match src zero:
    case ss True{}:
      ss
    case SNil{} False{}:
      SNil{}
    case SCon{_, tl} False{}:
      sdrop(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))

# a U32 compares equal to itself
law u32_eq_refl:
  for +uu: U32
  {U32.is_eq(uu, uu) == True{} : Bool}

def u32_eq_refl(uu):
  match uu:
    case U32{ww}:
      rf = Equal.sym(Cmp, Word.cmp(32n, ww, ww), EQ{}, weq_refl(32n, ww))
      %rf : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# U32s whose predecessors differ differ
law u32_ne_pred:
  for +aa: U32
  for +bb: U32
  for h_ne: {U32.is_eq(U32.sub(aa, 1), U32.sub(bb, 1)) == False{} : Bool}
  for bc: Bool
  for ec: {U32.is_eq(aa, bb) == bc : Bool}
  {U32.is_eq(aa, bb) == False{} : Bool}

def u32_ne_pred(aa, bb, h_ne, bc, ec):
  match bc:
    case False{}:
      ec
    case True{}:
      eab = ueq(aa, bb, ec)
      pre = Equal.cong(U32, Bool, xx => U32.is_eq(U32.sub(aa, 1), U32.sub(xx, 1)), aa, bb, eab)
      same = Equal.trans(Bool, True{}, U32.is_eq(U32.sub(aa, 1), U32.sub(aa, 1)), U32.is_eq(U32.sub(aa, 1),
        U32.sub(bb, 1)),
        Equal.sym(Bool, U32.is_eq(U32.sub(aa, 1), U32.sub(aa, 1)), True{}, u32_eq_refl(U32.sub(aa, 1))), pre)
      Empty.absurd({U32.is_eq(aa, bb) == False{} : Bool},
        true_false(Equal.trans(Bool, True{}, U32.is_eq(U32.sub(aa, 1), U32.sub(bb, 1)), False{}, same, h_ne)))

# SNil, and nothing else
def snil(txt: String) -> Bool:
  match txt:
    case SNil{}:
      True{}
    case SCon{_, _}:
      False{}

# the empty string is no character followed by more
law nil_cons:
  for -cc: Char
  for -rest: String
  for ee: {SNil{} == SCon{cc, rest} : String}
  Empty

def nil_cons(cc, rest, ee):
  true_false(Equal.cong(String, Bool, xx => snil(xx), SNil{}, SCon{cc, rest}, ee))

# zero differs from a U32 that is not zero
law zero_ne:
  for +nn: U32
  for +bb: U32
  for e0: {nn == 0 : U32}
  for h_nz: {Bool.not(U32.is_zero(bb)) == True{} : Bool}
  for bc: Bool
  for ec: {U32.is_eq(nn, bb) == bc : Bool}
  {U32.is_eq(nn, bb) == False{} : Bool}

def zero_ne(nn, bb, e0, h_nz, bc, ec):
  match bc:
    case False{}:
      ec
    case True{}:
      b0 = Equal.trans(U32, bb, nn, 0, Equal.sym(U32, nn, bb, ueq(nn, bb, ec)), e0)
      nz = Equal.cong(U32, Bool, xx => Bool.not(U32.is_zero(xx)), bb, 0, b0)
      Empty.absurd({U32.is_eq(nn, bb) == False{} : Bool},
        true_false(Equal.trans(Bool, True{}, Bool.not(U32.is_zero(bb)), False{}, Equal.sym(Bool,
          Bool.not(U32.is_zero(bb)), True{}, h_nz), nz)))

# pos_ne at the first character: position 0, and bb is not zero
law pos_ne.head:
  for +nn: U32
  for +bb: U32
  for -tl: String
  for e0: {nn == 0 : U32}
  for got: ({Bool.not(U32.is_zero(bb)) == True{} : Bool} & {Laws.bounded(tl, U32.sub(bb, 1)) == True{} : Bool})
  {U32.is_eq(nn, bb) == False{} : Bool}

def pos_ne.head(nn, bb, _tl, e0, got):
  (nz, _hb) = got
  zero_ne(nn, bb, e0, nz, U32.is_eq(nn, bb), {==})

# pos_ne past the first character, the rest given
law pos_ne.tail:
  for +nn: U32
  for +bb: U32
  for -tl: String
  for got: ({Bool.not(U32.is_zero(bb)) == True{} : Bool} & {Laws.bounded(tl, U32.sub(bb, 1)) == True{} : Bool})
  for ih: {Laws.bounded(tl, U32.sub(bb, 1)) == True{} : Bool}
    -> {U32.is_eq(U32.sub(nn, 1), U32.sub(bb, 1)) == False{} : Bool}
  {U32.is_eq(nn, bb) == False{} : Bool}

def pos_ne.tail(nn, bb, _tl, got, ih):
  (_nz, hb) = got
  u32_ne_pred(nn, bb, ih(hb), U32.is_eq(nn, bb), {==})

# a position that holds a character, in a text of at most bb characters, is not bb
law pos_ne:
  for +cut: String
  for +nn: U32
  for +bb: U32
  for zz: Bool
  for ez: {U32.is_zero(nn) == zz : Bool}
  for h_b: {Laws.bounded(cut, bb) == True{} : Bool}
  for cc: Char
  for rest: String
  for h_d: {sdrop(cut, nn, zz) == SCon{cc, rest} : String}
  {U32.is_eq(nn, bb) == False{} : Bool}

def pos_ne(cut, nn, bb, zz, ez, h_b, cc, rest, h_d):
  match cut zz:
    case SNil{} True{}:
      Empty.absurd({U32.is_eq(nn, bb) == False{} : Bool}, nil_cons(cc, rest, h_d))
    case SNil{} False{}:
      Empty.absurd({U32.is_eq(nn, bb) == False{} : Bool}, nil_cons(cc, rest, h_d))
    case SCon{hd, tl} True{}:
      pos_ne.head(nn, bb, tl, ueq(nn, 0, ez), and_both(Bool.not(U32.is_zero(bb)), Laws.bounded(tl, U32.sub(bb, 1)),
        h_b))
    case SCon{hd, tl} False{}:
      pos_ne.tail(nn, bb, tl, and_both(Bool.not(U32.is_zero(bb)), Laws.bounded(tl, U32.sub(bb, 1)), h_b),
        hh => pos_ne(tl, U32.sub(nn, 1), U32.sub(bb, 1), U32.is_zero(U32.sub(nn, 1)), {==}, hh, cc, rest, h_d))

# one less than a nonzero U32 is not the top
law pred_ne_top:
  for +bb: U32
  for h_nz: {Bool.not(U32.is_zero(bb)) == True{} : Bool}
  for bc: Bool
  for ec: {U32.is_eq(U32.sub(bb, 1), 4294967295) == bc : Bool}
  {U32.is_eq(U32.sub(bb, 1), 4294967295) == False{} : Bool}

def pred_ne_top(bb, h_nz, bc, ec):
  match bc:
    case False{}:
      ec
    case True{}:
      et = ueq(U32.sub(bb, 1), 4294967295, ec)
      up = Equal.cong(U32, U32, xx => U32.add(xx, 1), U32.sub(bb, 1), 4294967295, et)
      b0 = Equal.trans(U32, bb, U32.add(U32.sub(bb, 1), 1), 0, Equal.sym(U32, U32.add(U32.sub(bb, 1), 1), bb,
        u32_inc_dec(bb)), up)
      nz = Equal.cong(U32, Bool, xx => Bool.not(U32.is_zero(xx)), bb, 0, b0)
      Empty.absurd({U32.is_eq(U32.sub(bb, 1), 4294967295) == False{} : Bool},
        true_false(Equal.trans(Bool, True{}, Bool.not(U32.is_zero(bb)), False{},
          Equal.sym(Bool, Bool.not(U32.is_zero(bb)), True{}, h_nz), nz)))

# bounded_mono past the first character, the rest given
law bounded_mono.cons:
  for -tl: String
  for +bb: U32
  for h_top: {U32.is_eq(bb, 4294967295) == False{} : Bool}
  for got: ({Bool.not(U32.is_zero(bb)) == True{} : Bool} & {Laws.bounded(tl, U32.sub(bb, 1)) == True{} : Bool})
  for ih: {U32.is_eq(U32.sub(bb, 1), 4294967295) == False{} : Bool} -> {Laws.bounded(tl, U32.sub(bb,
    1)) == True{} : Bool}
    -> {Laws.bounded(tl, U32.add(U32.sub(bb, 1), 1)) == True{} : Bool}
  {Bool.and(Bool.not(U32.is_zero(U32.add(bb, 1))), Laws.bounded(tl, U32.sub(U32.add(bb, 1), 1))) == True{} : Bool}

def bounded_mono.cons(tl, bb, h_top, got, ih):
  (nz, hb) = got
  z1 = Equal.sym(Bool, U32.is_zero(U32.add(bb, 1)), False{}, inc_nonzero(bb, h_top))
  %z1 : {Bool.and(Bool.not(_), Laws.bounded(tl, U32.sub(U32.add(bb, 1), 1))) == True{} : Bool}
  d1 = Equal.sym(U32, U32.sub(U32.add(bb, 1), 1), bb, u32_dec_inc(bb))
  %d1 : {Bool.and(True{}, Laws.bounded(tl, _)) == True{} : Bool}
  i1 = u32_inc_dec(bb)
  %i1 : {Bool.and(True{}, Laws.bounded(tl, _)) == True{} : Bool}
  ih(pred_ne_top(bb, nz, U32.is_eq(U32.sub(bb, 1), 4294967295), {==}), hb)

# a text within bb characters is within bb + 1, below the top
law bounded_mono:
  for +txt: String
  for +bb: U32
  for h_top: {U32.is_eq(bb, 4294967295) == False{} : Bool}
  for h_b: {Laws.bounded(txt, bb) == True{} : Bool}
  {Laws.bounded(txt, U32.add(bb, 1)) == True{} : Bool}

def bounded_mono(txt, bb, h_top, h_b):
  match txt:
    case SNil{}:
      {==}
    case SCon{hd, tl}:
      bounded_mono.cons(tl, bb, h_top, and_both(Bool.not(U32.is_zero(bb)), Laws.bounded(tl, U32.sub(bb, 1)), h_b),
        ht => hh => bounded_mono(tl, U32.sub(bb, 1), ht, hh))

# the rest of a short text is short
law short_tail:
  for +hd: Char
  for +tl: String
  for h_s: {Laws.short(SCon{hd, tl}) == True{} : Bool}
  {Laws.short(tl) == True{} : Bool}

def short_tail(_hd, tl, h_s):
  bounded_mono(tl, 4294967294, {==}, h_s)

# the first character of a string, alone
def first1(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{hd, _}:
      SCon{hd, SNil{}}

# a string without its first character
def rest1(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{_, tl}:
      tl

# a nonzero U32's zero test, as the negation span.str and sdrop need
law nz_of:
  for +nn: U32
  for ez: {U32.is_zero(nn) == False{} : Bool}
  {Bool.not(U32.is_zero(nn)) == True{} : Bool}

def nz_of(nn, ez):
  ee = Equal.sym(Bool, U32.is_zero(nn), False{}, ez)
  %ee : {Bool.not(_) == True{} : Bool}
  {==}

# a span of no characters is empty
law span_zero:
  for +txt: String
  {V.span.str(txt, 0, True{}) == "" : String}

def span_zero(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

# a span one longer, past the first character, the rest given
law span_grow.cons:
  for +hd: Char
  for +tl: String
  for +nn: U32
  for +ez: {U32.is_zero(nn) == False{} : Bool}
  for h_top: {U32.is_eq(nn, 4294967295) == False{} : Bool}
  for cc: Char
  for ih: {V.span.str(tl, U32.add(U32.sub(nn, 1), 1), U32.is_zero(U32.add(U32.sub(nn, 1), 1)))
    == V.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))) ++ SCon{cc, SNil{}} : String}
  {V.span.str(SCon{hd, tl}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)))
    == V.span.str(SCon{hd, tl}, nn, False{}) ++ SCon{cc, SNil{}} : String}

def span_grow.cons(hd, tl, nn, _ez, h_top, cc, ih):
  z1 = Equal.sym(Bool, U32.is_zero(U32.add(nn, 1)), False{}, inc_nonzero(nn, h_top))
  %z1 : {V.span.str(SCon{hd, tl}, U32.add(nn, 1), _) == V.span.str(SCon{hd, tl}, nn, False{}) ++ SCon{cc,
    SNil{}} : String}
  d1 = Equal.sym(U32, U32.sub(U32.add(nn, 1), 1), nn, u32_dec_inc(nn))
  %d1 : {SCon{hd, V.span.str(tl, _, U32.is_zero(_))}
    == SCon{hd, V.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))) ++ SCon{cc, SNil{}}} : String}
  i1 = u32_inc_dec(nn)
  %i1 : {SCon{hd, V.span.str(tl, _, U32.is_zero(_))}
    == SCon{hd, V.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))) ++ SCon{cc, SNil{}}} : String}
  Equal.cong(String, String, xx => SCon{hd, xx},
    V.span.str(tl, U32.add(U32.sub(nn, 1), 1), U32.is_zero(U32.add(U32.sub(nn, 1), 1))),
    V.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))) ++ SCon{cc, SNil{}}, ih)

# a span one longer is the span and the next character, below the top
law span_grow:
  for +cut: String
  for +nn: U32
  for zz: Bool
  for +ez: {U32.is_zero(nn) == zz : Bool}
  for h_top: {U32.is_eq(nn, 4294967295) == False{} : Bool}
  for +cc: Char
  for rest: String
  for h_d: {sdrop(cut, nn, zz) == SCon{cc, rest} : String}
  {V.span.str(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == V.span.str(cut, nn, zz) ++ SCon{cc, SNil{}} : String}

def span_grow(cut, nn, zz, ez, h_top, cc, rest, h_d):
  match cut zz:
    case SNil{} True{}:
      Empty.absurd({V.span.str(SNil{}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == SNil{} ++ SCon{cc,
        SNil{}} : String},
        nil_cons(cc, rest, h_d))
    case SNil{} False{}:
      Empty.absurd({V.span.str(SNil{}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == SNil{} ++ SCon{cc,
        SNil{}} : String},
        nil_cons(cc, rest, h_d))
    case SCon{hd, tl} True{}:
      e0 = Equal.sym(U32, nn, 0, ueq(nn, 0, ez))
      %e0 : {V.span.str(SCon{hd, tl}, U32.add(_, 1), U32.is_zero(U32.add(_, 1))) == SCon{cc, SNil{}} : String}
      sz = Equal.sym(String, V.span.str(tl, 0, True{}), "", span_zero(tl))
      %sz : {SCon{hd, _} == SCon{cc, SNil{}} : String}
      Equal.cong(String, String, xx => first1(xx), SCon{hd, tl}, SCon{cc, rest}, h_d)
    case SCon{hd, tl} False{}:
      span_grow.cons(hd, tl, nn, ez, h_top, cc,
        span_grow(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), {==},
          pred_ne_top(nn, nz_of(nn, ez), U32.is_eq(U32.sub(nn, 1), 4294967295), {==}), cc, rest, h_d))

# nothing dropped is the whole string
law sdrop_zero:
  for +txt: String
  for rest: String
  for ee: {txt == rest : String}
  {sdrop(txt, 0, True{}) == rest : String}

def sdrop_zero(txt, _rest, ee):
  match txt:
    case SNil{}:
      ee
    case SCon{_, _}:
      ee

# what is left after a span one longer, past the first character, the rest given
law sdrop_grow.cons:
  for +hd: Char
  for +tl: String
  for +nn: U32
  for h_top: {U32.is_eq(nn, 4294967295) == False{} : Bool}
  for rest: String
  for ih: {sdrop(tl, U32.add(U32.sub(nn, 1), 1), U32.is_zero(U32.add(U32.sub(nn, 1), 1))) == rest : String}
  {sdrop(SCon{hd, tl}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == rest : String}

def sdrop_grow.cons(hd, tl, nn, h_top, rest, ih):
  z1 = Equal.sym(Bool, U32.is_zero(U32.add(nn, 1)), False{}, inc_nonzero(nn, h_top))
  %z1 : {sdrop(SCon{hd, tl}, U32.add(nn, 1), _) == rest : String}
  d1 = Equal.sym(U32, U32.sub(U32.add(nn, 1), 1), nn, u32_dec_inc(nn))
  %d1 : {sdrop(tl, _, U32.is_zero(_)) == rest : String}
  i1 = u32_inc_dec(nn)
  %i1 : {sdrop(tl, _, U32.is_zero(_)) == rest : String}
  ih

# what is left after a span one longer is what followed its next character
law sdrop_grow:
  for +cut: String
  for +nn: U32
  for zz: Bool
  for +ez: {U32.is_zero(nn) == zz : Bool}
  for h_top: {U32.is_eq(nn, 4294967295) == False{} : Bool}
  for cc: Char
  for +rest: String
  for h_d: {sdrop(cut, nn, zz) == SCon{cc, rest} : String}
  {sdrop(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == rest : String}

def sdrop_grow(cut, nn, zz, ez, h_top, cc, rest, h_d):
  match cut zz:
    case SNil{} True{}:
      Empty.absurd({sdrop(SNil{}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == rest : String}, nil_cons(cc, rest,
        h_d))
    case SNil{} False{}:
      Empty.absurd({sdrop(SNil{}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == rest : String}, nil_cons(cc, rest,
        h_d))
    case SCon{hd, tl} True{}:
      e0 = Equal.sym(U32, nn, 0, ueq(nn, 0, ez))
      %e0 : {sdrop(SCon{hd, tl}, U32.add(_, 1), U32.is_zero(U32.add(_, 1))) == rest : String}
      sdrop_zero(tl, rest, Equal.cong(String, String, xx => rest1(xx), SCon{hd, tl}, SCon{cc, rest}, h_d))
    case SCon{hd, tl} False{}:
      sdrop_grow.cons(hd, tl, nn, h_top, rest,
        sdrop_grow(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), {==},
          pred_ne_top(nn, nz_of(nn, ez), U32.is_eq(U32.sub(nn, 1), 4294967295), {==}), cc, rest, h_d))

# WP-L1: the character machine only adds tokens in front of those it is given

# a lexer state with more tokens after its own
def lex.app(lx: Lex.Lex, tt: List<&2, Lex.Tok>) -> Lex.Lex:
  match lx:
    case Lex.Lex{md, bf, tk}:
      Lex.Lex{md, bf, List.append(&2, Lex.Tok, tk, tt)}

# escape.put passes its tokens through
law pass.escape_put:
  for mb: Maybe<&2, Char>
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.escape.put(mb, bf, tt) == lex.app(Lex.escape.put(mb, bf, []), tt) : Lex.Lex}

def pass.escape_put(mb, _bf, _tt):
  match mb:
    case Some{_}:
      {==}
    case None{}:
      {==}

# escape.go passes its tokens through
law pass.escape_go:
  for +ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for is_u: Bool
  {Lex.escape.go(ch, bf, tt, is_u) == lex.app(Lex.escape.go(ch, bf, [], is_u), tt) : Lex.Lex}

def pass.escape_go(ch, bf, tt, is_u):
  match is_u:
    case True{}:
      {==}
    case False{}:
      pass.escape_put(Lex.unescape(ch), bf, tt)

# escape passes its tokens through
law pass.escape:
  for +ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.escape(ch, bf, tt) == lex.app(Lex.escape(ch, bf, []), tt) : Lex.Lex}

def pass.escape(ch, bf, tt):
  pass.escape_go(ch, bf, tt, U32.is_eq(Char.to_u32(ch), 117))

# unicode.end.go passes its tokens through
law pass.end_go:
  for cp: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for key: Lex.Sur
  {Lex.unicode.end.go(cp, bf, tt, key) == lex.app(Lex.unicode.end.go(cp, bf, [], key), tt) : Lex.Lex}

def pass.end_go(_cp, _bf, _tt, key):
  match key:
    case Lex.SOk{}:
      {==}
    case Lex.SHi{}:
      {==}
    case Lex.SLo{}:
      {==}

# unicode.put passes its tokens through
law pass.put:
  for left: Nat
  for +acc: U32
  for +dig: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.unicode.put(left, acc, dig, bf, tt) == lex.app(Lex.unicode.put(left, acc, dig, bf, []), tt) : Lex.Lex}

def pass.put(left, acc, dig, bf, tt):
  match left:
    case 0n:
      pass.end_go((acc * 16 + dig : U32), bf, tt, Lex.unicode.sur((acc * 16 + dig : U32)))
    case 1n+_:
      {==}

# unicode.go passes its tokens through
law pass.uni_go:
  for left: Nat
  for acc: U32
  for ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for ok: Bool
  {Lex.unicode.go(left, acc, ch, bf, tt, ok) == lex.app(Lex.unicode.go(left, acc, ch, bf, [], ok), tt) : Lex.Lex}

def pass.uni_go(left, acc, ch, bf, tt, ok):
  match ok:
    case True{}:
      pass.put(left, acc, Lex.hex(ch), bf, tt)
    case False{}:
      {==}

# unicode.low.end.go passes its tokens through
law pass.low_end_go:
  for lo: U32
  for hi: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for key: Lex.Sur
  {Lex.unicode.low.end.go(lo, hi, bf, tt, key) == lex.app(Lex.unicode.low.end.go(lo, hi, bf, [], key), tt) : Lex.Lex}

def pass.low_end_go(_lo, _hi, _bf, _tt, key):
  match key:
    case Lex.SLo{}:
      {==}
    case Lex.SOk{}:
      {==}
    case Lex.SHi{}:
      {==}

# unicode.low.put passes its tokens through
law pass.low_put:
  for left: Nat
  for +acc: U32
  for hi: U32
  for +dig: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.unicode.low.put(left, acc, hi, dig, bf, tt) == lex.app(Lex.unicode.low.put(left, acc, hi, dig, bf, []),
    tt) : Lex.Lex}

def pass.low_put(left, acc, hi, dig, bf, tt):
  match left:
    case 0n:
      pass.low_end_go((acc * 16 + dig : U32), hi, bf, tt, Lex.unicode.sur((acc * 16 + dig : U32)))
    case 1n+_:
      {==}

# unicode.low.go passes its tokens through
law pass.low_go:
  for left: Nat
  for acc: U32
  for hi: U32
  for ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for ok: Bool
  {Lex.unicode.low.go(left, acc, hi, ch, bf, tt, ok) == lex.app(Lex.unicode.low.go(left, acc, hi, ch, bf, [], ok),
    tt) : Lex.Lex}

def pass.low_go(left, acc, hi, ch, bf, tt, ok):
  match ok:
    case True{}:
      pass.low_put(left, acc, hi, Lex.hex(ch), bf, tt)
    case False{}:
      {==}

# step.str.go passes its tokens through
law pass.str_go:
  for ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for ctrl: Bool
  {Lex.step.str.go(ch, bf, tt, ctrl) == lex.app(Lex.step.str.go(ch, bf, [], ctrl), tt) : Lex.Lex}

def pass.str_go(_ch, _bf, _tt, ctrl):
  match ctrl:
    case True{}:
      {==}
    case False{}:
      {==}

# step.hi.go passes its tokens through
law pass.hi_go:
  for hi: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for slash: Bool
  {Lex.step.hi.go(hi, bf, tt, slash) == lex.app(Lex.step.hi.go(hi, bf, [], slash), tt) : Lex.Lex}

def pass.hi_go(_hi, _bf, _tt, slash):
  match slash:
    case True{}:
      {==}
    case False{}:
      {==}

# step.hiesc.go passes its tokens through
law pass.hiesc_go:
  for hi: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for is_u: Bool
  {Lex.step.hiesc.go(hi, bf, tt, is_u) == lex.app(Lex.step.hiesc.go(hi, bf, [], is_u), tt) : Lex.Lex}

def pass.hiesc_go(_hi, _bf, _tt, is_u):
  match is_u:
    case True{}:
      {==}
    case False{}:
      {==}

# step.hiesc passes its tokens through
law pass.hiesc:
  for hi: U32
  for ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.step.hiesc(hi, ch, bf, tt) == lex.app(Lex.step.hiesc(hi, ch, bf, []), tt) : Lex.Lex}

def pass.hiesc(hi, ch, bf, tt):
  pass.hiesc_go(hi, bf, tt, U32.is_eq(Char.to_u32(ch), 117))

# step passes its tokens through, after the ones it adds
law pass.step:
  for md: Lex.Mode
  for cls: Lex.Class
  for +ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.step(md, cls, ch, bf, tt) == lex.app(Lex.step(md, cls, ch, bf, []), tt) : Lex.Lex}

def pass.step(md, cls, ch, bf, tt):
  match md cls:
    case Lex.Idle{} Lex.CPunct{_}:
      {==}
    case Lex.Idle{} Lex.CQuote{}:
      {==}
    case Lex.Idle{} Lex.CSpace{}:
      {==}
    case Lex.Idle{} Lex.CBack{}:
      {==}
    case Lex.Idle{} Lex.COther{}:
      {==}
    case Lex.Word{} Lex.CPunct{_}:
      {==}
    case Lex.Word{} Lex.CQuote{}:
      {==}
    case Lex.Word{} Lex.CSpace{}:
      {==}
    case Lex.Word{} Lex.CBack{}:
      {==}
    case Lex.Word{} Lex.COther{}:
      {==}
    case Lex.Str{} Lex.CQuote{}:
      {==}
    case Lex.Str{} Lex.CBack{}:
      {==}
    case Lex.Str{} Lex.CPunct{_}:
      pass.str_go(ch, bf, tt, U32.is_lt(Char.to_u32(ch), 32))
    case Lex.Str{} Lex.CSpace{}:
      pass.str_go(ch, bf, tt, U32.is_lt(Char.to_u32(ch), 32))
    case Lex.Str{} Lex.COther{}:
      pass.str_go(ch, bf, tt, U32.is_lt(Char.to_u32(ch), 32))
    case Lex.Esc{} _:
      pass.escape(ch, bf, tt)
    case Lex.Uni{left, acc} _:
      pass.uni_go(left, acc, ch, bf, tt, Lex.hex.ok(Char.to_u32(ch)))
    case Lex.Hi{hi} _:
      pass.hi_go(hi, bf, tt, U32.is_eq(Char.to_u32(ch), 92))
    case Lex.HiEsc{hi} _:
      pass.hiesc(hi, ch, bf, tt)
    case Lex.Lo{left, acc, hi} _:
      pass.low_go(left, acc, hi, ch, bf, tt, Lex.hex.ok(Char.to_u32(ch)))
    case Lex.Bad{} _:
      {==}

# feed passes its tokens through, after the ones it adds
law pass.feed:
  for +ch: Char
  for md: Lex.Mode
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.feed(ch, Lex.Lex{md, bf, tt}) == lex.app(Lex.feed(ch, Lex.Lex{md, bf, []}), tt) : Lex.Lex}

def pass.feed(ch, md, bf, tt):
  pass.step(md, Lex.classify(ch), ch, bf, tt)

# a token with a span replaced by the characters it covers
def den(tok: Lex.Tok) -> Lex.Tok:
  match tok:
    case Lex.TStrS{cut, +nn}:
      Lex.TStr{V.span.str(cut, nn, U32.is_zero(nn))}
    case Lex.TWordS{cut, +nn}:
      Lex.TWord{V.span.str(cut, nn, U32.is_zero(nn))}
    case other:
      other

# tokens with their spans replaced
def dens(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case hd <> tl:
      den(hd) <> dens(tl)

# a lexer state with its tokens' spans replaced
def dlex(lx: Lex.Lex) -> Lex.Lex:
  match lx:
    case Lex.Lex{md, bf, tk}:
      Lex.Lex{md, bf, dens(tk)}

# replacing spans goes through an append
law dens_app:
  for +aa: List<&2, Lex.Tok>
  for bb: List<&2, Lex.Tok>
  {dens(List.append(&2, Lex.Tok, aa, bb)) == List.append(&2, Lex.Tok, dens(aa), dens(bb)) : List<&2, Lex.Tok>}

def dens_app(aa, bb):
  match aa:
    case Nil{}:
      {==}
    case hd <> tl:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, xx => den(hd) <> xx,
        dens(List.append(&2, Lex.Tok, tl, bb)), List.append(&2, Lex.Tok, dens(tl), dens(bb)), dens_app(tl, bb))

# replacing spans goes through a reversal
law dens_rev:
  for +aa: List<&2, Lex.Tok>
  for acc: List<&2, Lex.Tok>
  {dens(List.reverse.go(&2, Lex.Tok, aa, acc)) == List.reverse.go(&2, Lex.Tok, dens(aa), dens(acc)) : List<&2, Lex.Tok>}

def dens_rev(aa, acc):
  match aa:
    case Nil{}:
      {==}
    case hd <> tl:
      dens_rev(tl, hd <> acc)

# replacing spans goes through lex.app
law dlex_app:
  for lx: Lex.Lex
  for tt: List<&2, Lex.Tok>
  {dlex(lex.app(lx, tt)) == lex.app(dlex(lx), dens(tt)) : Lex.Lex}

def dlex_app(lx, tt):
  match lx:
    case Lex.Lex{md, bf, tk}:
      Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{md, bf, xx},
        dens(List.append(&2, Lex.Tok, tk, tt)), List.append(&2, Lex.Tok, dens(tk), dens(tt)), dens_app(tk, tt))

# the tokens a finished lexer gives, with spans replaced, depend only on its
# state with spans replaced
law dens_finish:
  for lx: Lex.Lex
  {dens(Lex.finish(lx)) == Lex.finish(dlex(lx)) : List<&2, Lex.Tok>}

def dens_finish(lx):
  match lx:
    case Lex.Lex{Lex.Idle{}, bf, tk}:
      dens_rev(tk, [])
    case Lex.Lex{Lex.Word{}, bf, tk}:
      dens_rev(Lex.TWord{Lex.text(bf)} <> tk, [])
    case Lex.Lex{Lex.Str{}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.Esc{}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.Uni{_, _}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.Hi{_}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.HiEsc{_}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.Lo{_, _, _}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.Bad{}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])

# feed as a function of a lexer state with its spans replaced
def feedg(+ch: Char, lx: Lex.Lex) -> Lex.Lex:
  match lx:
    case Lex.Lex{md, bf, dd}:
      lex.app(dlex(Lex.feed(ch, Lex.Lex{md, bf, []})), dd)

# feeding, then replacing spans, is feedg of the replaced state
law dlex_feed_g:
  for +ch: Char
  for +lx: Lex.Lex
  {dlex(Lex.feed(ch, lx)) == feedg(ch, dlex(lx)) : Lex.Lex}

def dlex_feed_g(ch, lx):
  match lx:
    case Lex.Lex{md, bf, tk}:
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, Lex.Lex{md, bf, tk})), dlex(lex.app(Lex.feed(ch, Lex.Lex{md, bf, []}),
        tk)),
        lex.app(dlex(Lex.feed(ch, Lex.Lex{md, bf, []})), dens(tk)),
        Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.feed(ch, Lex.Lex{md, bf, tk}),
          lex.app(Lex.feed(ch, Lex.Lex{md, bf, []}), tk), pass.feed(ch, md, bf, tk)),
        dlex_app(Lex.feed(ch, Lex.Lex{md, bf, []}), tk))

# two lexer states the same up to spans stay so after one character
law dlex_feed:
  for +ch: Char
  for +l1: Lex.Lex
  for +l2: Lex.Lex
  for ee: {dlex(l1) == dlex(l2) : Lex.Lex}
  {dlex(Lex.feed(ch, l1)) == dlex(Lex.feed(ch, l2)) : Lex.Lex}

def dlex_feed(ch, l1, l2, ee):
  Equal.trans(Lex.Lex, dlex(Lex.feed(ch, l1)), feedg(ch, dlex(l2)), dlex(Lex.feed(ch, l2)),
    Equal.trans(Lex.Lex, dlex(Lex.feed(ch, l1)), feedg(ch, dlex(l1)), feedg(ch, dlex(l2)),
      dlex_feed_g(ch, l1), Equal.cong(Lex.Lex, Lex.Lex, xx => feedg(ch, xx), dlex(l1), dlex(l2), ee)),
    Equal.sym(Lex.Lex, dlex(Lex.feed(ch, l2)), feedg(ch, dlex(l2)), dlex_feed_g(ch, l2)))

# appending nothing
law append_nil:
  for +txt: String
  {txt ++ "" == txt : String}

def append_nil(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{hd, tl}:
      Equal.cong(String, String, xx => SCon{hd, xx}, tl ++ "", tl, append_nil(tl))

# a reversed prefix of no characters is the accumulator
law rev_zero:
  for +src: String
  for +nn: U32
  for acc: List<&2, Char>
  {Lex.tokens.rev(src, nn, True{}, acc) == acc : List<&2, Char>}

def rev_zero(src, _nn, _acc):
  match src:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

# a span of no characters is empty, whatever the count
law span_true:
  for +src: String
  for +nn: U32
  {V.span.str(src, nn, True{}) == "" : String}

def span_true(src, _nn):
  match src:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

# reading a reversed prefix back gives the span's characters, in order
law text_rev:
  for +src: String
  for +nn: U32
  for zz: Bool
  for acc: List<&2, Char>
  for aa: String
  {Lex.text.go(Lex.tokens.rev(src, nn, zz, acc), aa) == Lex.text.go(acc, V.span.str(src, nn, zz) ++ aa) : String}

def text_rev(src, nn, zz, acc, aa):
  match src zz:
    case ss True{}:
      rz = Equal.sym(List<&2, Char>, Lex.tokens.rev(ss, nn, True{}, acc), acc, rev_zero(ss, nn, acc))
      %rz : {Lex.text.go(_, aa) == Lex.text.go(acc, V.span.str(ss, nn, True{}) ++ aa) : String}
      st = Equal.sym(String, V.span.str(ss, nn, True{}), "", span_true(ss, nn))
      %st : {Lex.text.go(acc, aa) == Lex.text.go(acc, _ ++ aa) : String}
      {==}
    case SNil{} False{}:
      {==}
    case SCon{hd, tl} False{}:
      text_rev(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hd <> acc, aa)

# the text of a reversed prefix is the span
law text_span:
  for +src: String
  for +nn: U32
  for +zz: Bool
  {Lex.text(Lex.tokens.rev(src, nn, zz, [])) == V.span.str(src, nn, zz) : String}

def text_span(src, nn, zz):
  Equal.trans(String, Lex.text(Lex.tokens.rev(src, nn, zz, [])), V.span.str(src, nn, zz) ++ "", V.span.str(src, nn, zz),
    text_rev(src, nn, zz, [], ""), append_nil(V.span.str(src, nn, zz)))

# the first character of a string, or U+0000
def head0(txt: String) -> Char:
  match txt:
    case SNil{}:
      Char.from_u32(0)
    case SCon{hd, _}:
      hd

# a reversed prefix one longer, past the first character, the rest given
law rev_grow.cons:
  for +hd: Char
  for +tl: String
  for +nn: U32
  for h_top: {U32.is_eq(nn, 4294967295) == False{} : Bool}
  for cc: Char
  for +acc: List<&2, Char>
  for ih: {Lex.tokens.rev(tl, U32.add(U32.sub(nn, 1), 1), U32.is_zero(U32.add(U32.sub(nn, 1), 1)), hd <> acc)
    == cc <> Lex.tokens.rev(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hd <> acc) : List<&2, Char>}
  {Lex.tokens.rev(SCon{hd, tl}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), acc)
    == cc <> Lex.tokens.rev(SCon{hd, tl}, nn, False{}, acc) : List<&2, Char>}

def rev_grow.cons(hd, tl, nn, h_top, cc, acc, ih):
  z1 = Equal.sym(Bool, U32.is_zero(U32.add(nn, 1)), False{}, inc_nonzero(nn, h_top))
  %z1 : {Lex.tokens.rev(SCon{hd, tl}, U32.add(nn, 1), _, acc)
    == cc <> Lex.tokens.rev(SCon{hd, tl}, nn, False{}, acc) : List<&2, Char>}
  d1 = Equal.sym(U32, U32.sub(U32.add(nn, 1), 1), nn, u32_dec_inc(nn))
  %d1 : {Lex.tokens.rev(tl, _, U32.is_zero(_), hd <> acc)
    == cc <> Lex.tokens.rev(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hd <> acc) : List<&2, Char>}
  i1 = u32_inc_dec(nn)
  %i1 : {Lex.tokens.rev(tl, _, U32.is_zero(_), hd <> acc)
    == cc <> Lex.tokens.rev(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hd <> acc) : List<&2, Char>}
  ih

# a reversed prefix one longer is the next character in front, below the top
law rev_grow:
  for +cut: String
  for +nn: U32
  for zz: Bool
  for +ez: {U32.is_zero(nn) == zz : Bool}
  for h_top: {U32.is_eq(nn, 4294967295) == False{} : Bool}
  for +cc: Char
  for rest: String
  for h_d: {sdrop(cut, nn, zz) == SCon{cc, rest} : String}
  for +acc: List<&2, Char>
  {Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), acc)
    == cc <> Lex.tokens.rev(cut, nn, zz, acc) : List<&2, Char>}

def rev_grow(cut, nn, zz, ez, h_top, cc, rest, h_d, acc):
  match cut zz:
    case SNil{} True{}:
      Empty.absurd({Lex.tokens.rev(SNil{}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), acc)
        == cc <> Lex.tokens.rev(SNil{}, nn, True{}, acc) : List<&2, Char>}, nil_cons(cc, rest, h_d))
    case SNil{} False{}:
      Empty.absurd({Lex.tokens.rev(SNil{}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), acc)
        == cc <> Lex.tokens.rev(SNil{}, nn, False{}, acc) : List<&2, Char>}, nil_cons(cc, rest, h_d))
    case SCon{hd, tl} True{}:
      e0 = Equal.sym(U32, nn, 0, ueq(nn, 0, ez))
      %e0 : {Lex.tokens.rev(SCon{hd, tl}, U32.add(_, 1), U32.is_zero(U32.add(_, 1)), acc) == cc <> acc : List<&2, Char>}
      rz = Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, hd <> acc), hd <> acc, rev_zero(tl, 0, hd <> acc))
      %rz : {_ == cc <> acc : List<&2, Char>}
      Equal.cong(Char, List<&2, Char>, xx => xx <> acc, hd, cc,
        Equal.cong(String, Char, xx => head0(xx), SCon{hd, tl}, SCon{cc, rest}, h_d))
    case SCon{hd, tl} False{}:
      rev_grow.cons(hd, tl, nn, h_top, cc, acc,
        rev_grow(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), {==},
          pred_ne_top(nn, nz_of(nn, ez), U32.is_eq(U32.sub(nn, 1), 4294967295), {==}), cc, rest, h_d, hd <> acc))

# whether a class is Lex.CQuote{}
def is_quote(cls: Lex.Class) -> Bool:
  match cls:
    case Lex.CQuote{}:
      True{}
    case _:
      False{}

# the last test of classify: a character past them all is COther, not Lex.CQuote{}
law cls_quote_end:
  for +cp: U32
  for h_c: {Lex.COther{} == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_end(cp, h_c):
  Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.COther{},
    Lex.CQuote{}, h_c)))

# classify's test for 9, once its answer is named
law cls_quote_11:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 9) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Lex.COther{}) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_11(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.CSpace{},
        Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_end(cp, h_c)

# classify's test for 13, once its answer is named
law cls_quote_10:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 13) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_10(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.CSpace{},
        Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_11(cp, U32.is_eq(cp, 9), {==}, h_c)

# classify's test for 10, once its answer is named
law cls_quote_9:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 10) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_9(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.CSpace{},
        Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_10(cp, U32.is_eq(cp, 13), {==}, h_c)

# classify's test for 32, once its answer is named
law cls_quote_8:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 32) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
      Lex.COther{})))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_8(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.CSpace{},
        Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_9(cp, U32.is_eq(cp, 10), {==}, h_c)

# classify's test for 92, once its answer is named
law cls_quote_7:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 92) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_7(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.CBack{},
        Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_8(cp, U32.is_eq(cp, 32), {==}, h_c)

# classify's test for 34, once its answer is named
law cls_quote_6:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 34) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
        Lex.COther{})))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_6(cp, bb, eb, h_c):
  match bb:
    case True{}:
      ueq(cp, 34, eb)
    case False{}:
      cls_quote_7(cp, U32.is_eq(cp, 92), {==}, h_c)

# classify's test for 44, once its answer is named
law cls_quote_5:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 44) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
        Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_5(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TComma{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_6(cp, U32.is_eq(cp, 34), {==}, h_c)

# classify's test for 58, once its answer is named
law cls_quote_4:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 58) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
    Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class,
      U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class,
        U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{})))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_4(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TColon{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_5(cp, U32.is_eq(cp, 44), {==}, h_c)

# classify's test for 125, once its answer is named
law cls_quote_3:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 125) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58),
    Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class,
      U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class,
        U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
            Lex.COther{}))))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_3(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TCloseObj{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_4(cp, U32.is_eq(cp, 58), {==}, h_c)

# classify's test for 123, once its answer is named
law cls_quote_2:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 123) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 125),
    Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34),
        Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32),
          Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13),
            Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
              Lex.COther{})))))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_2(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TOpenObj{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_3(cp, U32.is_eq(cp, 125), {==}, h_c)

# classify's test for 93, once its answer is named
law cls_quote_1:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 93) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 123),
    Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
        Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class,
            U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
              Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_1(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TCloseArr{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_2(cp, U32.is_eq(cp, 123), {==}, h_c)

# classify's test for 91, once its answer is named
law cls_quote_0:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 91) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 93),
    Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 123), Lex.CPunct{Lex.TOpenObj{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58),
        Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}},
          Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{},
            Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10),
              Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp,
                9), Lex.CSpace{}, Lex.COther{})))))))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_0(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TOpenArr{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_1(cp, U32.is_eq(cp, 93), {==}, h_c)

# a character classify reads as Lex.CQuote{} is code point 34
law cls_quote:
  for +ch: Char
  for h_c: {Lex.classify(ch) == Lex.CQuote{} : Lex.Class}
  {Char.to_u32(ch) == 34 : U32}

def cls_quote(ch, h_c):
  cls_quote_0(Char.to_u32(ch), U32.is_eq(Char.to_u32(ch), 91), {==}, h_c)

# whether a class is Lex.CBack{}
def is_back(cls: Lex.Class) -> Bool:
  match cls:
    case Lex.CBack{}:
      True{}
    case _:
      False{}

# the last test of classify: a character past them all is COther, not Lex.CBack{}
law cls_back_end:
  for +cp: U32
  for h_c: {Lex.COther{} == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_end(cp, h_c):
  Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.COther{}, Lex.CBack{},
    h_c)))

# classify's test for 9, once its answer is named
law cls_back_11:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 9) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Lex.COther{}) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_11(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.CSpace{},
        Lex.CBack{}, h_c)))
    case False{}:
      cls_back_end(cp, h_c)

# classify's test for 13, once its answer is named
law cls_back_10:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 13) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_10(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.CSpace{},
        Lex.CBack{}, h_c)))
    case False{}:
      cls_back_11(cp, U32.is_eq(cp, 9), {==}, h_c)

# classify's test for 10, once its answer is named
law cls_back_9:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 10) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_9(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.CSpace{},
        Lex.CBack{}, h_c)))
    case False{}:
      cls_back_10(cp, U32.is_eq(cp, 13), {==}, h_c)

# classify's test for 32, once its answer is named
law cls_back_8:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 32) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
      Lex.COther{})))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_8(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.CSpace{},
        Lex.CBack{}, h_c)))
    case False{}:
      cls_back_9(cp, U32.is_eq(cp, 10), {==}, h_c)

# classify's test for 92, once its answer is named
law cls_back_7:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 92) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_7(cp, bb, eb, h_c):
  match bb:
    case True{}:
      ueq(cp, 92, eb)
    case False{}:
      cls_back_8(cp, U32.is_eq(cp, 32), {==}, h_c)

# classify's test for 34, once its answer is named
law cls_back_6:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 34) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
        Lex.COther{})))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_6(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.CQuote{},
        Lex.CBack{}, h_c)))
    case False{}:
      cls_back_7(cp, U32.is_eq(cp, 92), {==}, h_c)

# classify's test for 44, once its answer is named
law cls_back_5:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 44) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
        Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_5(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TComma{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_6(cp, U32.is_eq(cp, 34), {==}, h_c)

# classify's test for 58, once its answer is named
law cls_back_4:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 58) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
    Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class,
      U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class,
        U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{})))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_4(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TColon{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_5(cp, U32.is_eq(cp, 44), {==}, h_c)

# classify's test for 125, once its answer is named
law cls_back_3:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 125) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58),
    Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class,
      U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class,
        U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
            Lex.COther{}))))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_3(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TCloseObj{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_4(cp, U32.is_eq(cp, 58), {==}, h_c)

# classify's test for 123, once its answer is named
law cls_back_2:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 123) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 125),
    Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34),
        Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32),
          Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13),
            Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
              Lex.COther{})))))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_2(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TOpenObj{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_3(cp, U32.is_eq(cp, 125), {==}, h_c)

# classify's test for 93, once its answer is named
law cls_back_1:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 93) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 123),
    Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
        Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class,
            U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
              Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_1(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TCloseArr{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_2(cp, U32.is_eq(cp, 123), {==}, h_c)

# classify's test for 91, once its answer is named
law cls_back_0:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 91) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 93),
    Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 123), Lex.CPunct{Lex.TOpenObj{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58),
        Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}},
          Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{},
            Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10),
              Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp,
                9), Lex.CSpace{}, Lex.COther{})))))))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_0(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TOpenArr{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_1(cp, U32.is_eq(cp, 93), {==}, h_c)

# a character classify reads as Lex.CBack{} is code point 92
law cls_back:
  for +ch: Char
  for h_c: {Lex.classify(ch) == Lex.CBack{} : Lex.Class}
  {Char.to_u32(ch) == 92 : U32}

def cls_back(ch, h_c):
  cls_back_0(Char.to_u32(ch), U32.is_eq(Char.to_u32(ch), 91), {==}, h_c)

# WP-L1: the span scanner against the character machine. rel says what a
# scanner state and a lexer state have in common: the same tokens up to
# spans, and a span that holds exactly the reversed buffer

# rel for a span scanner state, by its mode
def rel.go(+cut: String, +nn: U32, md: Lex.Span, +toks: List<&2, Lex.Tok>, lx: Lex.Lex, ss: String) -> Type:
  match md:
    case Lex.GIdle{}:
      {dlex(lx) == Lex.Lex{Lex.Idle{}, [], dens(toks)} : Lex.Lex}
    case Lex.GWord{}:
      ({dlex(lx) == Lex.Lex{Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), dens(toks)} : Lex.Lex}
        & ({sdrop(cut, nn, U32.is_zero(nn)) == ss : String} & {Laws.short(cut) == True{} : Bool}))
    case Lex.GStr{}:
      ({dlex(lx) == Lex.Lex{Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), dens(toks)} : Lex.Lex}
        & ({sdrop(cut, nn, U32.is_zero(nn)) == ss : String} & {Laws.short(cut) == True{} : Bool}))
    case Lex.GBad{}:
      {dlex(lx) == Lex.Lex{Lex.Bad{}, [], dens(toks)} : Lex.Lex}

# what a span scanner state and a lexer state share, with `ss` left to read
def rel(sc: Lex.Scan, lx: Lex.Lex, ss: String) -> Type:
  match sc:
    case Lex.Go{cut, nn, md, toks}:
      rel.go(cut, nn, md, toks, lx, ss)
    case Lex.Old{ol}:
      {dlex(lx) == dlex(ol) : Lex.Lex}

# feed, with the character's class named
law feed_as:
  for +ch: Char
  for md: Lex.Mode
  for bf: List<&2, Char>
  for tk: List<&2, Lex.Tok>
  for cls: Lex.Class
  for ecls: {Lex.classify(ch) == cls : Lex.Class}
  {Lex.feed(ch, Lex.Lex{md, bf, tk}) == Lex.step(md, cls, ch, bf, tk) : Lex.Lex}

def feed_as(ch, md, bf, tk, cls, ecls):
  ec = Equal.sym(Lex.Class, Lex.classify(ch), cls, ecls)
  %ec : {Lex.step(md, _, ch, bf, tk) == Lex.step(md, cls, ch, bf, tk) : Lex.Lex}
  {==}

# a lexer state the same as Lex{md, bf, tk} up to spans, fed one character
law via:
  for +ch: Char
  for +lx: Lex.Lex
  for +md: Lex.Mode
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for cls: Lex.Class
  for ecls: {Lex.classify(ch) == cls : Lex.Class}
  for hr: {dlex(lx) == Lex.Lex{md, bf, dens(tk)} : Lex.Lex}
  {dlex(Lex.feed(ch, lx)) == dlex(Lex.step(md, cls, ch, bf, tk)) : Lex.Lex}

def via(ch, lx, md, bf, tk, cls, ecls, hr):
  Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.feed(ch, Lex.Lex{md, bf, tk})), dlex(Lex.step(md, cls, ch,
    bf, tk)),
    dlex_feed(ch, lx, Lex.Lex{md, bf, tk}, hr),
    Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.feed(ch, Lex.Lex{md, bf, tk}), Lex.step(md, cls, ch, bf, tk),
      feed_as(ch, md, bf, tk, cls, ecls)))

# step.str, with the control test named
law str_as:
  for +ch: Char
  for bf: List<&2, Char>
  for tk: List<&2, Lex.Tok>
  for ctl: Bool
  for ectl: {U32.is_lt(Char.to_u32(ch), 32) == ctl : Bool}
  {Lex.step.str(ch, bf, tk) == Lex.step.str.go(ch, bf, tk, ctl) : Lex.Lex}

def str_as(ch, bf, tk, ctl, ectl):
  ec = Equal.sym(Bool, U32.is_lt(Char.to_u32(ch), 32), ctl, ectl)
  %ec : {Lex.step.str.go(ch, bf, tk, _) == Lex.step.str.go(ch, bf, tk, ctl) : Lex.Lex}
  {==}

# a quote or a backslash is not a control character
law not_ctl:
  for +ch: Char
  for kk: U32
  for ek: {Char.to_u32(ch) == kk : U32}
  for h_kk: {U32.is_lt(kk, 32) == False{} : Bool}
  for ectl: {U32.is_lt(Char.to_u32(ch), 32) == True{} : Bool}
  Empty

def not_ctl(ch, kk, ek, h_kk, ectl):
  lt = Equal.cong(U32, Bool, xx => U32.is_lt(xx, 32), Char.to_u32(ch), kk, ek)
  true_false(Equal.trans(Bool, True{}, U32.is_lt(kk, 32), False{},
    Equal.trans(Bool, True{}, U32.is_lt(Char.to_u32(ch), 32), U32.is_lt(kk, 32), Equal.sym(Bool,
      U32.is_lt(Char.to_u32(ch), 32), True{}, ectl), lt),
    h_kk))

# a word or string span grown by one character, from the step's lexer state
law grow_rel:
  for +ch: Char
  for +tl: String
  for +cut: String
  for +nn: U32
  for +toks: List<&2, Lex.Tok>
  for -lx: Lex.Lex
  for +md: Lex.Mode
  for +hd: {sdrop(cut, nn, U32.is_zero(nn)) == SCon{ch, tl} : String}
  for +hs: {Laws.short(cut) == True{} : Bool}
  for hf: {dlex(Lex.feed(ch, lx)) == Lex.Lex{md, ch <> Lex.tokens.rev(cut, nn, U32.is_zero(nn), []),
    dens(toks)} : Lex.Lex}
  ({dlex(Lex.feed(ch, lx)) == Lex.Lex{md, Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []),
    dens(toks)} : Lex.Lex}
    & ({sdrop(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == tl : String} & {Laws.short(cut) == True{} : Bool}))

def grow_rel(ch, tl, cut, nn, toks, lx, md, hd, hs, hf):
  +top = pos_ne(cut, nn, 4294967295, U32.is_zero(nn), {==}, hs, ch, tl, hd)
  rg = rev_grow(cut, nn, U32.is_zero(nn), {==}, top, ch, tl, hd, [])
  (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{md, ch <> Lex.tokens.rev(cut, nn, U32.is_zero(nn), []),
    dens(toks)},
      Lex.Lex{md, Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []), dens(toks)}, hf,
      Equal.cong(List<&2, Char>, Lex.Lex, xx => Lex.Lex{md, xx, dens(toks)}, ch <> Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []),
        Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []),
        Equal.sym(List<&2, Char>, Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []),
          ch <> Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), rg))),
    (sdrop_grow(cut, nn, U32.is_zero(nn), {==}, top, ch, tl, hd), hs))

# a string opened after a word: its empty buffer, and the word's span as text
law two_cong:
  for +tl: String
  for aa: String
  for bb: String
  for ee: {aa == bb : String}
  for +toks: List<&2, Lex.Tok>
  {Lex.Lex{Lex.Str{}, [], Lex.TWord{aa} <> dens(toks)} == Lex.Lex{Lex.Str{}, Lex.tokens.rev(tl, 0, True{}, []),
    Lex.TWord{bb} <> dens(toks)}
    : Lex.Lex}

def two_cong(tl, aa, bb, ee, toks):
  rz = Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, []), [], rev_zero(tl, 0, []))
  %rz : {Lex.Lex{Lex.Str{}, [], Lex.TWord{aa} <> dens(toks)} == Lex.Lex{Lex.Str{}, _,
    Lex.TWord{bb} <> dens(toks)} : Lex.Lex}
  %ee : {Lex.Lex{Lex.Str{}, [], Lex.TWord{aa} <> dens(toks)} == Lex.Lex{Lex.Str{}, [],
    Lex.TWord{_} <> dens(toks)} : Lex.Lex}
  {==}

# one character of the span scanner and of the character machine, with its
# class and its control test named
law rel_hit:
  for +ch: Char
  for +tl: String
  for +cut: String
  for +nn: U32
  for md: Lex.Span
  for +toks: List<&2, Lex.Tok>
  for +lx: Lex.Lex
  for cls: Lex.Class
  for +ecls: {Lex.classify(ch) == cls : Lex.Class}
  for ctl: Bool
  for +ectl: {U32.is_lt(Char.to_u32(ch), 32) == ctl : Bool}
  for h_r: rel.go(cut, nn, md, toks, lx, SCon{ch, tl})
  for +h_s: {Laws.short(SCon{ch, tl}) == True{} : Bool}
  rel(Lex.tokens.hit(ch, tl, cut, nn, md, toks, cls, ctl), Lex.feed(ch, lx), tl)

def rel_hit(ch, tl, cut, nn, md, toks, lx, cls, ecls, ctl, ectl, h_r, h_s):
  match md cls ctl:
    case Lex.GIdle{} Lex.CPunct{pp} True{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CPunct{pp}, ecls, h_r)
    case Lex.GBad{} Lex.CPunct{pp} True{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CPunct{pp}, ecls, h_r)
    case Lex.GWord{} Lex.CPunct{pp} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Idle{}, [],
        den(pp) <> Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), []))} <> dens(toks)},
          Lex.Lex{Lex.Idle{}, [], den(pp) <> Lex.TWord{V.span.str(cut, nn, U32.is_zero(nn))} <> dens(toks)}, via(ch,
            lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CPunct{pp}, ecls, eq),
          Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], den(pp) <> Lex.TWord{xx} <> dens(toks)},
            Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
              text_span(cut, nn, U32.is_zero(nn))))
    case Lex.GStr{} Lex.CPunct{pp} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
        []), toks)), Lex.Lex{Lex.Bad{}, [], dens(toks)},
          via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CPunct{pp}, ecls, eq),
          Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []),
            toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}),
            str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}, ectl)))
    case Lex.GIdle{} Lex.CPunct{pp} False{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CPunct{pp}, ecls, h_r)
    case Lex.GBad{} Lex.CPunct{pp} False{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CPunct{pp}, ecls, h_r)
    case Lex.GWord{} Lex.CPunct{pp} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Idle{}, [],
        den(pp) <> Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), []))} <> dens(toks)},
          Lex.Lex{Lex.Idle{}, [], den(pp) <> Lex.TWord{V.span.str(cut, nn, U32.is_zero(nn))} <> dens(toks)}, via(ch,
            lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CPunct{pp}, ecls, eq),
          Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], den(pp) <> Lex.TWord{xx} <> dens(toks)},
            Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
              text_span(cut, nn, U32.is_zero(nn))))
    case Lex.GStr{} Lex.CPunct{pp} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      grow_rel(ch, tl, cut, nn, toks, lx, Lex.Str{}, hd, hs,
          Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
            []), toks)), dlex(Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{})),
            via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CPunct{pp}, ecls, eq),
            Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
              []), toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}),
              str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}, ectl))))
    case Lex.GIdle{} Lex.CQuote{} True{}:
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [], dens(toks)},
            Lex.Lex{Lex.Str{}, Lex.tokens.rev(tl, 0, True{}, []), dens(toks)}, via(ch, lx, Lex.Idle{}, [], toks,
              Lex.CQuote{}, ecls, h_r),
            Equal.cong(List<&2, Char>, Lex.Lex, xx => Lex.Lex{Lex.Str{}, xx, dens(toks)}, [], Lex.tokens.rev(tl, 0,
              True{}, []),
              Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, []), [], rev_zero(tl, 0, [])))),
          (sdrop_zero(tl, tl, {==}), short_tail(ch, tl, h_s)))
    case Lex.GBad{} Lex.CQuote{} True{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CQuote{}, ecls, h_r)
    case Lex.GWord{} Lex.CQuote{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []))} <> dens(toks)},
            Lex.Lex{Lex.Str{}, Lex.tokens.rev(tl, 0, True{}, []), Lex.TWord{V.span.str(cut, nn,
              U32.is_zero(nn))} <> dens(toks)},
            Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [],
              Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), []))} <> dens(toks)},
              Lex.Lex{Lex.Str{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn),
                []))} <> dens(toks)}, via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks,
                  Lex.CQuote{}, ecls, eq), {==}),
            two_cong(tl, Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn,
              U32.is_zero(nn)), text_span(cut, nn, U32.is_zero(nn)), toks)),
          (sdrop_zero(tl, tl, {==}), short_tail(ch, tl, h_s)))
    case Lex.GStr{} Lex.CQuote{} True{}:
      Empty.absurd(rel(Lex.tokens.hit(ch, tl, cut, nn, Lex.GStr{}, toks, Lex.CQuote{}, True{}), Lex.feed(ch, lx),
        tl), not_ctl(ch, 34, cls_quote(ch, ecls), {==}, ectl))
    case Lex.GIdle{} Lex.CQuote{} False{}:
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [], dens(toks)},
            Lex.Lex{Lex.Str{}, Lex.tokens.rev(tl, 0, True{}, []), dens(toks)}, via(ch, lx, Lex.Idle{}, [], toks,
              Lex.CQuote{}, ecls, h_r),
            Equal.cong(List<&2, Char>, Lex.Lex, xx => Lex.Lex{Lex.Str{}, xx, dens(toks)}, [], Lex.tokens.rev(tl, 0,
              True{}, []),
              Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, []), [], rev_zero(tl, 0, [])))),
          (sdrop_zero(tl, tl, {==}), short_tail(ch, tl, h_s)))
    case Lex.GBad{} Lex.CQuote{} False{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CQuote{}, ecls, h_r)
    case Lex.GWord{} Lex.CQuote{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []))} <> dens(toks)},
            Lex.Lex{Lex.Str{}, Lex.tokens.rev(tl, 0, True{}, []), Lex.TWord{V.span.str(cut, nn,
              U32.is_zero(nn))} <> dens(toks)},
            Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [],
              Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), []))} <> dens(toks)},
              Lex.Lex{Lex.Str{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn),
                []))} <> dens(toks)}, via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks,
                  Lex.CQuote{}, ecls, eq), {==}),
            two_cong(tl, Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn,
              U32.is_zero(nn)), text_span(cut, nn, U32.is_zero(nn)), toks)),
          (sdrop_zero(tl, tl, {==}), short_tail(ch, tl, h_s)))
    case Lex.GStr{} Lex.CQuote{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Idle{}, [], Lex.TStr{Lex.text(Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []))} <> dens(toks)},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{V.span.str(cut, nn, U32.is_zero(nn))} <> dens(toks)}, via(ch, lx,
            Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CQuote{}, ecls, eq),
          Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TStr{xx} <> dens(toks)},
            Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
              text_span(cut, nn, U32.is_zero(nn))))
    case Lex.GIdle{} Lex.CSpace{} True{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CSpace{}, ecls, h_r)
    case Lex.GBad{} Lex.CSpace{} True{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CSpace{}, ecls, h_r)
    case Lex.GWord{} Lex.CSpace{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Idle{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []))} <> dens(toks)},
          Lex.Lex{Lex.Idle{}, [], Lex.TWord{V.span.str(cut, nn, U32.is_zero(nn))} <> dens(toks)}, via(ch, lx,
            Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CSpace{}, ecls, eq),
          Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TWord{xx} <> dens(toks)},
            Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
              text_span(cut, nn, U32.is_zero(nn))))
    case Lex.GStr{} Lex.CSpace{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
        []), toks)), Lex.Lex{Lex.Bad{}, [], dens(toks)},
          via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CSpace{}, ecls, eq),
          Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []),
            toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}),
            str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}, ectl)))
    case Lex.GIdle{} Lex.CSpace{} False{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CSpace{}, ecls, h_r)
    case Lex.GBad{} Lex.CSpace{} False{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CSpace{}, ecls, h_r)
    case Lex.GWord{} Lex.CSpace{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Idle{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []))} <> dens(toks)},
          Lex.Lex{Lex.Idle{}, [], Lex.TWord{V.span.str(cut, nn, U32.is_zero(nn))} <> dens(toks)}, via(ch, lx,
            Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CSpace{}, ecls, eq),
          Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TWord{xx} <> dens(toks)},
            Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
              text_span(cut, nn, U32.is_zero(nn))))
    case Lex.GStr{} Lex.CSpace{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      grow_rel(ch, tl, cut, nn, toks, lx, Lex.Str{}, hd, hs,
          Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
            []), toks)), dlex(Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{})),
            via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CSpace{}, ecls, eq),
            Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
              []), toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}),
              str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}, ectl))))
    case Lex.GIdle{} Lex.CBack{} True{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CBack{}, ecls, h_r)
    case Lex.GBad{} Lex.CBack{} True{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CBack{}, ecls, h_r)
    case Lex.GWord{} Lex.CBack{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CBack{}, ecls, eq)
    case Lex.GStr{} Lex.CBack{} True{}:
      Empty.absurd(rel(Lex.tokens.hit(ch, tl, cut, nn, Lex.GStr{}, toks, Lex.CBack{}, True{}), Lex.feed(ch, lx), tl),
        not_ctl(ch, 92, cls_back(ch, ecls), {==}, ectl))
    case Lex.GIdle{} Lex.CBack{} False{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CBack{}, ecls, h_r)
    case Lex.GBad{} Lex.CBack{} False{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CBack{}, ecls, h_r)
    case Lex.GWord{} Lex.CBack{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CBack{}, ecls, eq)
    case Lex.GStr{} Lex.CBack{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CBack{}, ecls, eq)
    case Lex.GIdle{} Lex.COther{} True{}:
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Word{}, [ch], dens(toks)},
            Lex.Lex{Lex.Word{}, Lex.tokens.rev(tl, 0, True{}, [ch]), dens(toks)}, via(ch, lx, Lex.Idle{}, [], toks,
              Lex.COther{}, ecls, h_r),
            Equal.cong(List<&2, Char>, Lex.Lex, xx => Lex.Lex{Lex.Word{}, xx, dens(toks)}, [ch], Lex.tokens.rev(tl,
              0, True{}, [ch]),
              Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, [ch]), [ch], rev_zero(tl, 0, [ch])))),
          (sdrop_zero(tl, tl, {==}), h_s))
    case Lex.GBad{} Lex.COther{} True{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.COther{}, ecls, h_r)
    case Lex.GWord{} Lex.COther{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      grow_rel(ch, tl, cut, nn, toks, lx, Lex.Word{}, hd, hs, via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []), toks, Lex.COther{}, ecls, eq))
    case Lex.GStr{} Lex.COther{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
        []), toks)), Lex.Lex{Lex.Bad{}, [], dens(toks)},
          via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.COther{}, ecls, eq),
          Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []),
            toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}),
            str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}, ectl)))
    case Lex.GIdle{} Lex.COther{} False{}:
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Word{}, [ch], dens(toks)},
            Lex.Lex{Lex.Word{}, Lex.tokens.rev(tl, 0, True{}, [ch]), dens(toks)}, via(ch, lx, Lex.Idle{}, [], toks,
              Lex.COther{}, ecls, h_r),
            Equal.cong(List<&2, Char>, Lex.Lex, xx => Lex.Lex{Lex.Word{}, xx, dens(toks)}, [ch], Lex.tokens.rev(tl,
              0, True{}, [ch]),
              Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, [ch]), [ch], rev_zero(tl, 0, [ch])))),
          (sdrop_zero(tl, tl, {==}), h_s))
    case Lex.GBad{} Lex.COther{} False{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.COther{}, ecls, h_r)
    case Lex.GWord{} Lex.COther{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      grow_rel(ch, tl, cut, nn, toks, lx, Lex.Word{}, hd, hs, via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []), toks, Lex.COther{}, ecls, eq))
    case Lex.GStr{} Lex.COther{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      grow_rel(ch, tl, cut, nn, toks, lx, Lex.Str{}, hd, hs,
          Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
            []), toks)), dlex(Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{})),
            via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.COther{}, ecls, eq),
            Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
              []), toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}),
              str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}, ectl))))

# one character keeps a scanner state and a lexer state related
law rel_step:
  for +sc: Lex.Scan
  for +lx: Lex.Lex
  for +ch: Char
  for +tl: String
  for h_r: rel(sc, lx, SCon{ch, tl})
  for h_s: {Laws.short(SCon{ch, tl}) == True{} : Bool}
  rel(Lex.tokens.feed(ch, tl, sc), Lex.feed(ch, lx), tl)

def rel_step(sc, lx, ch, tl, h_r, h_s):
  match sc:
    case Lex.Old{ol}:
      dlex_feed(ch, lx, ol, h_r)
    case Lex.Go{cut, nn, md, toks}:
      rel_hit(ch, tl, cut, nn, md, toks, lx, Lex.classify(ch), {==}, U32.is_lt(Char.to_u32(ch), 32), {==}, h_r, h_s)

# the tokens at the end of a word, with spans replaced: the word's span as text
law end_word:
  for +cut: String
  for +nn: U32
  for +toks: List<&2, Lex.Tok>
  {dens(Lex.tokens.done(cut, nn, Lex.GWord{}, toks))
    == Lex.finish(Lex.Lex{Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), dens(toks)}) : List<&2, Lex.Tok>}

def end_word(cut, nn, toks):
  dr = dens_rev(Lex.TWordS{cut, nn} <> toks, [])
  ts = Equal.sym(String, Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
    text_span(cut, nn, U32.is_zero(nn)))
  %ts : {dens(Lex.tokens.done(cut, nn, Lex.GWord{}, toks))
    == List.reverse(&2, Lex.Tok, Lex.TWord{_} <> dens(toks)) : List<&2, Lex.Tok>}
  dr

# rel_end, once the scanner's tokens are known to be finish of a lexer state
# the same as lx up to spans
law rel_end.at:
  for -tks: List<&2, Lex.Tok>
  for -ls: Lex.Lex
  for +lx: Lex.Lex
  for et: {dens(tks) == Lex.finish(ls) : List<&2, Lex.Tok>}
  for hl: {dlex(lx) == ls : Lex.Lex}
  {dens(tks) == dens(Lex.finish(lx)) : List<&2, Lex.Tok>}

def rel_end.at(tks, ls, lx, et, hl):
  Equal.trans(List<&2, Lex.Tok>, dens(tks), Lex.finish(dlex(lx)), dens(Lex.finish(lx)),
    Equal.trans(List<&2, Lex.Tok>, dens(tks), Lex.finish(ls), Lex.finish(dlex(lx)), et,
      Equal.cong(Lex.Lex, List<&2, Lex.Tok>, xx => Lex.finish(xx), ls, dlex(lx), Equal.sym(Lex.Lex, dlex(lx), ls, hl))),
    Equal.sym(List<&2, Lex.Tok>, dens(Lex.finish(lx)), Lex.finish(dlex(lx)), dens_finish(lx)))

# at the end of the text, a scanner state and a lexer state give the same
# tokens up to spans
law rel_end:
  for sc: Lex.Scan
  for +lx: Lex.Lex
  for h_r: rel(sc, lx, "")
  {dens(Lex.tokens.end(sc)) == dens(Lex.finish(lx)) : List<&2, Lex.Tok>}

def rel_end(sc, lx, h_r):
  match sc:
    case Lex.Old{ol}:
      Equal.trans(List<&2, Lex.Tok>, dens(Lex.finish(ol)), Lex.finish(dlex(lx)), dens(Lex.finish(lx)),
        Equal.trans(List<&2, Lex.Tok>, dens(Lex.finish(ol)), Lex.finish(dlex(ol)), Lex.finish(dlex(lx)),
          dens_finish(ol),
          Equal.cong(Lex.Lex, List<&2, Lex.Tok>, xx => Lex.finish(xx), dlex(ol), dlex(lx), Equal.sym(Lex.Lex,
            dlex(lx), dlex(ol), h_r))),
        Equal.sym(List<&2, Lex.Tok>, dens(Lex.finish(lx)), Lex.finish(dlex(lx)), dens_finish(lx)))
    case Lex.Go{cut, nn, Lex.GIdle{}, toks}:
      rel_end.at(Lex.tokens.done(cut, nn, Lex.GIdle{}, toks), Lex.Lex{Lex.Idle{}, [], dens(toks)}, lx,
        dens_rev(toks, []), h_r)
    case Lex.Go{cut, nn, Lex.GWord{}, toks}:
      (eq, _more) = h_r
      rel_end.at(Lex.tokens.done(cut, nn, Lex.GWord{}, toks),
        Lex.Lex{Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), dens(toks)}, lx, end_word(cut, nn, toks), eq)
    case Lex.Go{cut, nn, Lex.GStr{}, toks}:
      (eq, _more) = h_r
      rel_end.at(Lex.tokens.done(cut, nn, Lex.GStr{}, toks),
        Lex.Lex{Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), dens(toks)}, lx,
          dens_rev(Lex.TBad{} <> toks, []), eq)
    case Lex.Go{cut, nn, Lex.GBad{}, toks}:
      rel_end.at(Lex.tokens.done(cut, nn, Lex.GBad{}, toks), Lex.Lex{Lex.Bad{}, [], dens(toks)}, lx,
        dens_rev(Lex.TBad{} <> toks, []), h_r)

# the span scanner and the character machine, run over the rest of a short
# text from related states, give the same tokens up to spans
law lex_agree_go:
  for +ss: String
  for +sc: Lex.Scan
  for +lx: Lex.Lex
  for h_r: rel(sc, lx, ss)
  for +h_s: {Laws.short(ss) == True{} : Bool}
  {dens(Lex.tokens.go(ss, sc)) == dens(Lex.finish(Lex.run(String.to_list(ss), lx))) : List<&2, Lex.Tok>}

def lex_agree_go(ss, sc, lx, h_r, h_s):
  match ss:
    case SNil{}:
      rel_end(sc, lx, h_r)
    case SCon{ch, tl}:
      lex_agree_go(tl, Lex.tokens.feed(ch, tl, sc), Lex.feed(ch, lx), rel_step(sc, lx, ch, tl, h_r, h_s),
        short_tail(ch, tl, h_s))

# WP-L1: for a text of at most 2^32 - 1 characters, the lexer's span path
# and its character path give the same tokens, once spans are replaced by the
# characters they cover
law lexers_agree:
  for +ss: String
  for h_s: {Laws.short(ss) == True{} : Bool}
  {dens(Lex.tokens(ss)) == dens(Lex.finish(Lex.run(String.to_list(ss), Lex.Lex{Lex.Idle{}, [], []}))) : List<&2,
    Lex.Tok>}

def lexers_agree(ss, h_s):
  lex_agree_go(ss, Lex.Go{"", 0, Lex.GIdle{}, []}, Lex.Lex{Lex.Idle{}, [], []}, {==}, h_s)

# WP-L2: the character lexer reads back what print writes

# a word of n zero bits
def zw(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+pp:
      WCon{False{}, zw(pp)}

# against a 0 bit, a word is below exactly when the bits above are
law lt_fin_f:
  for cc: Cmp
  for aa: Bool
  {Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)) == Cmp.is_lt(cc) : Bool}

def lt_fin_f(cc, aa):
  match cc:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      match aa:
        case False{}:
          {==}
        case True{}:
          {==}

# a word is never below zero
law zw_nlt:
  for n: Nat
  for ww: Word(n)
  {Cmp.is_lt(Word.cmp(n, ww, zw(n))) == False{} : Bool}

def zw_nlt(n, ww):
  match n:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{bb, +tt}:
          Equal.trans(Bool, Cmp.is_lt(Word.cmp.fin(bb, False{}, Word.cmp(pp, tt, zw(pp)))),
            Cmp.is_lt(Word.cmp(pp, tt, zw(pp))), False{}, lt_fin_f(Word.cmp(pp, tt, zw(pp)), bb), zw_nlt(pp, tt))

# below a word whose low bit is 0, the bits above are below
law lt_up:
  for aa: Bool
  for cc: Cmp
  for h_lt: {Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)) == True{} : Bool}
  {Cmp.is_lt(cc) == True{} : Bool}

def lt_up(aa, cc, h_lt):
  Equal.trans(Bool, Cmp.is_lt(cc), Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)), True{},
    Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)), Cmp.is_lt(cc), lt_fin_f(cc, aa)), h_lt)

# what lex_ctl says of a code point: its \u00XX escape reads back as itself
def ctl_goal(uu: U32, buf: List<&2, Char>, toks: List<&2, Lex.Tok>) -> Type:
  {Lex.run(String.to_list(Print.escape.u(uu)), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}

# a control's \u00XX escape, one control at a time
law lex_ctl5:
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for buf: List<&2, Char>
  for toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape.u(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{},
    zw(26n)}}}}}}})),
    Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, zw(26n)}}}}}}}} <> buf,
      toks} : Lex.Lex}

def lex_ctl5(b0, b1, b2, b3, b4, _buf, _toks):
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

# the control case, once bit 5 and the bits above are known
law lex_ctl.at:
  for cc: Cmp
  for b5: Bool
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for +rest: Word(26n)
  for ec: {Word.cmp(26n, rest, zw(26n)) == cc : Cmp}
  for h_lt: {Cmp.is_lt(Word.cmp.fin(b5, True{}, cc)) == True{} : Bool}
  for buf: List<&2, Char>
  for toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape.u(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}})),
    Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}} <> buf,
      toks} : Lex.Lex}

def lex_ctl.at(cc, b5, b0, b1, b2, b3, b4, rest, ec, h_lt, buf, toks):
  match cc:
    case LT{}:
      ez = Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, rest, zw(26n)), LT{}, ec)
      Empty.absurd(ctl_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}, buf, toks),
        true_false(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(26n, rest, zw(26n))), False{},
        Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, rest, zw(26n))), True{}, ez), zw_nlt(26n, rest))))
    case GT{}:
      match b5:
        case False{}:
          Empty.absurd(ctl_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}, buf, toks),
            false_true(h_lt))
        case True{}:
          Empty.absurd(ctl_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}, buf, toks),
            false_true(h_lt))
    case EQ{}:
      match b5:
        case True{}:
          Empty.absurd(ctl_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}, buf, toks),
            false_true(h_lt))
        case False{}:
          er = Equal.sym(Word(26n), rest, zw(26n),
            weq(26n, rest, zw(26n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(26n, rest, zw(26n)), EQ{}, ec)))
          %er : {Lex.run(String.to_list(Print.escape.u(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{},
            _}}}}}}})), Lex.Lex{Lex.Str{}, buf, toks}) ==
            Lex.Lex{Lex.Str{}, Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, _}}}}}}}} <> buf,
              toks} : Lex.Lex}
          lex_ctl5(b0, b1, b2, b3, b4, buf, toks)

# a code point below U+0020, written as \u00XX, reads back as itself
law lex_ctl:
  for +uu: U32
  for h_lt: {U32.is_lt(uu, 32) == True{} : Bool}
  for buf: List<&2, Char>
  for toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape.u(uu)), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}

def lex_ctl(uu, h_lt, buf, toks):
  match uu:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +rest}}}}}}}:
      +c5 = Word.cmp.fin(b5, True{}, Word.cmp(26n, rest, zw(26n)))
      +c4 = Word.cmp.fin(b4, False{}, c5)
      +c3 = Word.cmp.fin(b3, False{}, c4)
      +c2 = Word.cmp.fin(b2, False{}, c3)
      +c1 = Word.cmp.fin(b1, False{}, c2)
      h5 = lt_up(b4, c5, lt_up(b3, c4, lt_up(b2, c3, lt_up(b1, c2, lt_up(b0, c1, h_lt)))))
      lex_ctl.at(Word.cmp(26n, rest, zw(26n)), b5, b0, b1, b2, b3, b4, rest, {==}, h5, buf, toks)

# a string character that is none of `"`, `\` and the controls stays itself
law str_other:
  for cls: Lex.Class
  for +uu: U32
  for ecls: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  for e34: {U32.is_eq(uu, 34) == False{} : Bool}
  for e92: {U32.is_eq(uu, 92) == False{} : Bool}
  for ect: {U32.is_lt(uu, 32) == False{} : Bool}
  for buf: List<&2, Char>
  for toks: List<&2, Lex.Tok>
  {Lex.step(Lex.Str{}, cls, Chr{uu}, buf, toks) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}

def str_other(cls, uu, ecls, e34, e92, ect, buf, toks):
  match cls:
    case Lex.CQuote{}:
      Empty.absurd({Lex.step(Lex.Str{}, Lex.CQuote{}, Chr{uu}, buf, toks) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf,
        toks} : Lex.Lex},
        false_true(Equal.trans(Bool, False{}, U32.is_eq(uu, 34), True{}, Equal.sym(Bool, U32.is_eq(uu, 34), False{},
          e34),
          Equal.cong(U32, Bool, xx => U32.is_eq(xx, 34), uu, 34, cls_quote(Chr{uu}, ecls)))))
    case Lex.CBack{}:
      Empty.absurd({Lex.step(Lex.Str{}, Lex.CBack{}, Chr{uu}, buf, toks) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf,
        toks} : Lex.Lex},
        false_true(Equal.trans(Bool, False{}, U32.is_eq(uu, 92), True{}, Equal.sym(Bool, U32.is_eq(uu, 92), False{},
          e92),
          Equal.cong(U32, Bool, xx => U32.is_eq(xx, 92), uu, 92, cls_back(Chr{uu}, ecls)))))
    case Lex.CPunct{tt}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Lex.step.str.go(Chr{uu}, buf, toks, _) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}
      {==}
    case Lex.CSpace{}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Lex.step.str.go(Chr{uu}, buf, toks, _) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}
      {==}
    case Lex.COther{}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Lex.step.str.go(Chr{uu}, buf, toks, _) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}
      {==}

# escape.plain's answer, with each of its tests named, read back
law lex_plain:
  for b34: Bool
  for b92: Bool
  for b8: Bool
  for b12: Bool
  for b10: Bool
  for b13: Bool
  for b9: Bool
  for ct: Bool
  for +uu: U32
  for e34: {U32.is_eq(uu, 34) == b34 : Bool}
  for e92: {U32.is_eq(uu, 92) == b92 : Bool}
  for e8: {U32.is_eq(uu, 8) == b8 : Bool}
  for e12: {U32.is_eq(uu, 12) == b12 : Bool}
  for e10: {U32.is_eq(uu, 10) == b10 : Bool}
  for e13: {U32.is_eq(uu, 13) == b13 : Bool}
  for e9: {U32.is_eq(uu, 9) == b9 : Bool}
  for ect: {U32.is_lt(uu, 32) == ct : Bool}
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Bool.pick(String, b34, "\\\"", Bool.pick(String, b92, "\\\\", Bool.pick(String, b8, "\\b",
    Bool.pick(String, b12, "\\f", Bool.pick(String, b10, "\\n", Bool.pick(String, b13, "\\r", Bool.pick(String, b9,
    "\\t", Print.escape.rest.go(uu, Chr{uu}, ct))))))))), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}

def lex_plain(b34, b92, b8, b12, b10, b13, b9, ct, uu, e34, e92, e8, e12, e10, e13, e9, ect, buf, toks):
  match b34:
    case True{}:
      eu = Equal.sym(U32, uu, 34, ueq(uu, 34, e34))
      %eu : {Lex.run(String.to_list("\\\""), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{}, Chr{_} <> buf,
        toks} : Lex.Lex}
      {==}
    case False{}:
      match b92:
        case True{}:
          eu = Equal.sym(U32, uu, 92, ueq(uu, 92, e92))
          %eu : {Lex.run(String.to_list("\\\\"), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{}, Chr{_} <> buf,
            toks} : Lex.Lex}
          {==}
        case False{}:
          match b8:
            case True{}:
              eu = Equal.sym(U32, uu, 8, ueq(uu, 8, e8))
              %eu : {Lex.run(String.to_list("\\b"), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{}, Chr{_} <> buf,
                toks} : Lex.Lex}
              {==}
            case False{}:
              match b12:
                case True{}:
                  eu = Equal.sym(U32, uu, 12, ueq(uu, 12, e12))
                  %eu : {Lex.run(String.to_list("\\f"), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{},
                    Chr{_} <> buf, toks} : Lex.Lex}
                  {==}
                case False{}:
                  match b10:
                    case True{}:
                      eu = Equal.sym(U32, uu, 10, ueq(uu, 10, e10))
                      %eu : {Lex.run(String.to_list("\\n"), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{},
                        Chr{_} <> buf, toks} : Lex.Lex}
                      {==}
                    case False{}:
                      match b13:
                        case True{}:
                          eu = Equal.sym(U32, uu, 13, ueq(uu, 13, e13))
                          %eu : {Lex.run(String.to_list("\\r"), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{},
                            Chr{_} <> buf, toks} : Lex.Lex}
                          {==}
                        case False{}:
                          match b9:
                            case True{}:
                              eu = Equal.sym(U32, uu, 9, ueq(uu, 9, e9))
                              %eu : {Lex.run(String.to_list("\\t"), Lex.Lex{Lex.Str{}, buf,
                                toks}) == Lex.Lex{Lex.Str{}, Chr{_} <> buf, toks} : Lex.Lex}
                              {==}
                            case False{}:
                              match ct:
                                case True{}:
                                  lex_ctl(uu, ect, buf, toks)
                                case False{}:
                                  Equal.trans(Lex.Lex, Lex.feed(Chr{uu}, Lex.Lex{Lex.Str{}, buf, toks}),
                                      Lex.step(Lex.Str{}, Lex.classify(Chr{uu}), Chr{uu}, buf,
                                        toks), Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks},
                                      feed_as(Chr{uu}, Lex.Str{}, buf, toks, Lex.classify(Chr{uu}), {==}),
                                      str_other(Lex.classify(Chr{uu}), uu, {==}, e34, e92, ect, buf, toks))

# a character as print writes it back: itself when a scalar value, else U+FFFD
def fix(ch: Char) -> Char:
  match ch:
    case Chr{+uu}:
      Bool.pick(Char, Print.scalar(uu), Chr{uu}, Chr{65533})

# the characters, fixed, reversed onto buf
def fix_rev(cs: List<&2, Char>, buf: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      buf
    case Con{hd, tl}:
      fix_rev(tl, fix(hd) <> buf)

# the characters, fixed, as a string
def fixs(cs: List<&2, Char>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{hd, tl}:
      SCon{fix(hd), fixs(tl)}

# one character's escape, once it is known whether it is a scalar value
law lex_sc:
  for sc: Bool
  for +uu: U32
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape.scalar(uu, Chr{uu}, sc)), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Bool.pick(Char, sc, Chr{uu}, Chr{65533}) <> buf, toks} : Lex.Lex}

def lex_sc(sc, uu, buf, toks):
  match sc:
    case True{}:
      lex_plain(U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_eq(uu, 8), U32.is_eq(uu, 12), U32.is_eq(uu, 10),
        U32.is_eq(uu, 13), U32.is_eq(uu, 9), U32.is_lt(uu, 32), uu, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
        buf, toks)
    case False{}:
      {==}

# inside a string, a character print escapes reads back fixed
law lex_char:
  for +ch: Char
  for buf: List<&2, Char>
  for toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape.char(ch)), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, fix(ch) <> buf, toks} : Lex.Lex}

def lex_char(ch, buf, toks):
  match ch:
    case Chr{+uu}:
      lex_sc(Print.scalar(uu), uu, buf, toks)

# the character lexer on two strings is the lexer on the first, then the second
law run_app:
  for +aa: String
  for +bb: String
  for st: Lex.Lex
  {Lex.run(String.to_list(aa ++ bb), st) == Lex.run(String.to_list(bb), Lex.run(String.to_list(aa), st)) : Lex.Lex}

def run_app(aa, bb, st):
  match aa:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      run_app(tl, bb, Lex.feed(hd, st))

# inside a string, print's escape of the characters reads back fixed
law lex_esc:
  for +cs: List<&2, Char>
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape(cs)), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, fix_rev(cs, buf), toks} : Lex.Lex}

def lex_esc(cs, buf, toks):
  match cs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      Equal.trans(Lex.Lex,
        Lex.run(String.to_list(Print.escape.char(hd) ++ Print.escape(tl)), Lex.Lex{Lex.Str{}, buf, toks}),
        Lex.run(String.to_list(Print.escape(tl)), Lex.Lex{Lex.Str{}, fix(hd) <> buf, toks}),
        Lex.Lex{Lex.Str{}, fix_rev(tl, fix(hd) <> buf), toks},
        Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.escape.char(hd) ++ Print.escape(tl)), Lex.Lex{Lex.Str{}, buf, toks}),
          Lex.run(String.to_list(Print.escape(tl)), Lex.run(String.to_list(Print.escape.char(hd)),
            Lex.Lex{Lex.Str{}, buf, toks})),
          Lex.run(String.to_list(Print.escape(tl)), Lex.Lex{Lex.Str{}, fix(hd) <> buf, toks}),
          run_app(Print.escape.char(hd), Print.escape(tl), Lex.Lex{Lex.Str{}, buf, toks}),
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list(Print.escape(tl)), xx),
            Lex.run(String.to_list(Print.escape.char(hd)), Lex.Lex{Lex.Str{}, buf, toks}),
            Lex.Lex{Lex.Str{}, fix(hd) <> buf, toks}, lex_char(hd, buf, toks))),
        lex_esc(tl, fix(hd) <> buf, toks))

# a buffer of fixed characters, read back
law text_fix:
  for +cs: List<&2, Char>
  for +buf: List<&2, Char>
  for +acc: String
  {Lex.text.go(fix_rev(cs, buf), acc) == Lex.text.go(buf, fixs(cs) ++ acc) : String}

def text_fix(cs, buf, acc):
  match cs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      text_fix(tl, fix(hd) <> buf, acc)

# a quoted string, from between tokens, reads back as one string token of its
# characters, fixed
law lex_quote:
  for +txt: String
  for +toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.quote(txt)), Lex.Lex{Lex.Idle{}, [], toks}) ==
    Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(txt))} <> toks} : Lex.Lex}

def lex_quote(txt, toks):
  +cs = String.to_list(txt)
  +ee = Print.escape(cs)
  +fr = fix_rev(cs, [])
  Equal.trans(Lex.Lex,
    Lex.run(String.to_list("\"" ++ ee ++ "\""), Lex.Lex{Lex.Idle{}, [], toks}),
    Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, fr, toks}),
    Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(cs)} <> toks},
    Equal.trans(Lex.Lex,
      Lex.run(String.to_list("\"" ++ ee ++ "\""), Lex.Lex{Lex.Idle{}, [], toks}),
      Lex.run(String.to_list(ee ++ "\""), Lex.Lex{Lex.Str{}, [], toks}),
      Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, fr, toks}),
      run_app("\"", ee ++ "\"", Lex.Lex{Lex.Idle{}, [], toks}),
      Equal.trans(Lex.Lex,
        Lex.run(String.to_list(ee ++ "\""), Lex.Lex{Lex.Str{}, [], toks}),
        Lex.run(String.to_list("\""), Lex.run(String.to_list(ee), Lex.Lex{Lex.Str{}, [], toks})),
        Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, fr, toks}),
        run_app(ee, "\"", Lex.Lex{Lex.Str{}, [], toks}),
        Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("\""), xx), Lex.run(String.to_list(ee),
          Lex.Lex{Lex.Str{}, [], toks}),
          Lex.Lex{Lex.Str{}, fr, toks}, lex_esc(cs, [], toks)))),
    Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TStr{xx} <> toks}, Lex.text(fr), fixs(cs),
      Equal.trans(String, Lex.text.go(fr, ""), fixs(cs) ++ "", fixs(cs), text_fix(cs, [], ""),
        append_nil(fixs(cs)))))

# WP-L2, words: every character of a JSON number is a word character

# a character past all of classify's tests, with each test named: when a
# predicate holds of it and of none of the tested code points
law cls_other:
  for b91: Bool
  for b93: Bool
  for b123: Bool
  for b125: Bool
  for b58: Bool
  for b44: Bool
  for b34: Bool
  for b92: Bool
  for b32: Bool
  for b10: Bool
  for b13: Bool
  for b9: Bool
  for +cp: U32
  for pp: U32 -> Bool
  for e91: {U32.is_eq(cp, 91) == b91 : Bool}
  for e93: {U32.is_eq(cp, 93) == b93 : Bool}
  for e123: {U32.is_eq(cp, 123) == b123 : Bool}
  for e125: {U32.is_eq(cp, 125) == b125 : Bool}
  for e58: {U32.is_eq(cp, 58) == b58 : Bool}
  for e44: {U32.is_eq(cp, 44) == b44 : Bool}
  for e34: {U32.is_eq(cp, 34) == b34 : Bool}
  for e92: {U32.is_eq(cp, 92) == b92 : Bool}
  for e32: {U32.is_eq(cp, 32) == b32 : Bool}
  for e10: {U32.is_eq(cp, 10) == b10 : Bool}
  for e13: {U32.is_eq(cp, 13) == b13 : Bool}
  for e9: {U32.is_eq(cp, 9) == b9 : Bool}
  for h: {pp(cp) == True{} : Bool}
  for n91: {pp(91) == False{} : Bool}
  for n93: {pp(93) == False{} : Bool}
  for n123: {pp(123) == False{} : Bool}
  for n125: {pp(125) == False{} : Bool}
  for n58: {pp(58) == False{} : Bool}
  for n44: {pp(44) == False{} : Bool}
  for n34: {pp(34) == False{} : Bool}
  for n92: {pp(92) == False{} : Bool}
  for n32: {pp(32) == False{} : Bool}
  for n10: {pp(10) == False{} : Bool}
  for n13: {pp(13) == False{} : Bool}
  for n9: {pp(9) == False{} : Bool}
  {Bool.pick(Lex.Class, b91, Lex.CPunct{Lex.TOpenArr{}}, Bool.pick(Lex.Class, b93, Lex.CPunct{Lex.TCloseArr{}},
    Bool.pick(Lex.Class, b123, Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, b125, Lex.CPunct{Lex.TCloseObj{}},
    Bool.pick(Lex.Class, b58, Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, b44, Lex.CPunct{Lex.TComma{}},
    Bool.pick(Lex.Class, b34, Lex.CQuote{}, Bool.pick(Lex.Class, b92, Lex.CBack{}, Bool.pick(Lex.Class, b32,
    Lex.CSpace{}, Bool.pick(Lex.Class, b10, Lex.CSpace{}, Bool.pick(Lex.Class, b13, Lex.CSpace{}, Bool.pick(Lex.Class,
    b9, Lex.CSpace{}, Lex.COther{})))))))))))) == Lex.COther{} : Lex.Class}

def cls_other(
  b91,
  b93,
  b123,
  b125,
  b58,
  b44,
  b34,
  b92,
  b32,
  b10,
  b13,
  b9,
  cp,
  pp,
  e91,
  e93,
  e123,
  e125,
  e58,
  e44,
  e34,
  e92,
  e32,
  e10,
  e13,
  e9,
  h,
  n91,
  n93,
  n123,
  n125,
  n58,
  n44,
  n34,
  n92,
  n32,
  n10,
  n13,
  n9
):
  match b91:
    case True{}:
      Empty.absurd({Lex.CPunct{Lex.TOpenArr{}} == Lex.COther{} : Lex.Class}, true_false(Equal.trans(Bool, True{},
        pp(cp), False{},
        Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(91), False{},
          Equal.cong(U32, Bool, pp, cp, 91, ueq(cp, 91, e91)), n91))))
    case False{}:
      match b93:
        case True{}:
          Empty.absurd({Lex.CPunct{Lex.TCloseArr{}} == Lex.COther{} : Lex.Class}, true_false(Equal.trans(Bool, True{},
            pp(cp), False{},
            Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(93), False{},
              Equal.cong(U32, Bool, pp, cp, 93, ueq(cp, 93, e93)), n93))))
        case False{}:
          match b123:
            case True{}:
              Empty.absurd({Lex.CPunct{Lex.TOpenObj{}} == Lex.COther{} : Lex.Class}, true_false(Equal.trans(Bool,
                True{}, pp(cp), False{},
                Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(123), False{},
                  Equal.cong(U32, Bool, pp, cp, 123, ueq(cp, 123, e123)), n123))))
            case False{}:
              match b125:
                case True{}:
                  Empty.absurd({Lex.CPunct{Lex.TCloseObj{}} == Lex.COther{} : Lex.Class}, true_false(Equal.trans(Bool,
                    True{}, pp(cp), False{},
                    Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(125), False{},
                      Equal.cong(U32, Bool, pp, cp, 125, ueq(cp, 125, e125)), n125))))
                case False{}:
                  match b58:
                    case True{}:
                      Empty.absurd({Lex.CPunct{Lex.TColon{}} == Lex.COther{} : Lex.Class}, true_false(Equal.trans(Bool,
                        True{}, pp(cp), False{},
                        Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(58), False{},
                          Equal.cong(U32, Bool, pp, cp, 58, ueq(cp, 58, e58)), n58))))
                    case False{}:
                      match b44:
                        case True{}:
                          Empty.absurd({Lex.CPunct{Lex.TComma{}} == Lex.COther{} : Lex.Class},
                            true_false(Equal.trans(Bool, True{}, pp(cp), False{},
                            Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(44), False{},
                              Equal.cong(U32, Bool, pp, cp, 44, ueq(cp, 44, e44)), n44))))
                        case False{}:
                          match b34:
                            case True{}:
                              Empty.absurd({Lex.CQuote{} == Lex.COther{} : Lex.Class}, true_false(Equal.trans(Bool,
                                True{}, pp(cp), False{},
                                Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(34), False{},
                                  Equal.cong(U32, Bool, pp, cp, 34, ueq(cp, 34, e34)), n34))))
                            case False{}:
                              match b92:
                                case True{}:
                                  Empty.absurd({Lex.CBack{} == Lex.COther{} : Lex.Class}, true_false(Equal.trans(Bool,
                                    True{}, pp(cp), False{},
                                    Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(92), False{},
                                      Equal.cong(U32, Bool, pp, cp, 92, ueq(cp, 92, e92)), n92))))
                                case False{}:
                                  match b32:
                                    case True{}:
                                      Empty.absurd({Lex.CSpace{} == Lex.COther{} : Lex.Class},
                                        true_false(Equal.trans(Bool, True{}, pp(cp), False{},
                                        Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(32), False{},
                                          Equal.cong(U32, Bool, pp, cp, 32, ueq(cp, 32, e32)), n32))))
                                    case False{}:
                                      match b10:
                                        case True{}:
                                          Empty.absurd({Lex.CSpace{} == Lex.COther{} : Lex.Class},
                                            true_false(Equal.trans(Bool, True{}, pp(cp), False{},
                                            Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(10),
                                              False{},
                                              Equal.cong(U32, Bool, pp, cp, 10, ueq(cp, 10, e10)), n10))))
                                        case False{}:
                                          match b13:
                                            case True{}:
                                              Empty.absurd({Lex.CSpace{} == Lex.COther{} : Lex.Class},
                                                true_false(Equal.trans(Bool, True{}, pp(cp), False{},
                                                Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(13),
                                                  False{},
                                                  Equal.cong(U32, Bool, pp, cp, 13, ueq(cp, 13, e13)), n13))))
                                            case False{}:
                                              match b9:
                                                case True{}:
                                                  Empty.absurd({Lex.CSpace{} == Lex.COther{} : Lex.Class},
                                                    true_false(Equal.trans(Bool, True{}, pp(cp), False{},
                                                    Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp),
                                                      pp(9), False{},
                                                      Equal.cong(U32, Bool, pp, cp, 9, ueq(cp, 9, e9)), n9))))
                                                case False{}:
                                                  {==}

# a character a predicate holds of, where it holds of none of classify's code
# points, is a word character
law cls_by:
  for +ch: Char
  for pp: U32 -> Bool
  for h: {pp(Char.to_u32(ch)) == True{} : Bool}
  for n91: {pp(91) == False{} : Bool}
  for n93: {pp(93) == False{} : Bool}
  for n123: {pp(123) == False{} : Bool}
  for n125: {pp(125) == False{} : Bool}
  for n58: {pp(58) == False{} : Bool}
  for n44: {pp(44) == False{} : Bool}
  for n34: {pp(34) == False{} : Bool}
  for n92: {pp(92) == False{} : Bool}
  for n32: {pp(32) == False{} : Bool}
  for n10: {pp(10) == False{} : Bool}
  for n13: {pp(13) == False{} : Bool}
  for n9: {pp(9) == False{} : Bool}
  {Lex.classify(ch) == Lex.COther{} : Lex.Class}

def cls_by(ch, pp, h, n91, n93, n123, n125, n58, n44, n34, n92, n32, n10, n13, n9):
  +cp = Char.to_u32(ch)
  cls_other(U32.is_eq(cp, 91), U32.is_eq(cp, 93), U32.is_eq(cp, 123), U32.is_eq(cp, 125), U32.is_eq(cp, 58),
    U32.is_eq(cp, 44), U32.is_eq(cp, 34), U32.is_eq(cp, 92), U32.is_eq(cp, 32), U32.is_eq(cp, 10), U32.is_eq(cp,
    13), U32.is_eq(cp, 9),
    cp, pp, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, h, n91, n93, n123, n125, n58, n44,
      n34, n92, n32, n10, n13, n9)

# every character is a word character
def others(cs: List<&2, Char>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case Con{hd, tl}:
      ({Lex.classify(hd) == Lex.COther{} : Lex.Class} & others(tl))

# a digit is a word character
law oth_digit:
  for +ch: Char
  for h: {Laws.digit(ch) == True{} : Bool}
  {Lex.classify(ch) == Lex.COther{} : Lex.Class}

def oth_digit(ch, h):
  cls_by(ch, xx => V.num.ok.digit(xx), h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# digit1-9 is a word character
law oth_digit19:
  for +ch: Char
  for h: {Laws.digit19(ch) == True{} : Bool}
  {Lex.classify(ch) == Lex.COther{} : Lex.Class}

def oth_digit19(ch, h):
  cls_by(ch, xx => V.num.ok.lead(xx), h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a character that is one given word code point is a word character
law oth_cp:
  for +ch: Char
  for kk: U32
  for h: {Laws.is_cp(ch, kk) == True{} : Bool}
  for hk: {Lex.classify.go(kk) == Lex.COther{} : Lex.Class}
  {Lex.classify(ch) == Lex.COther{} : Lex.Class}

def oth_cp(ch, kk, h, hk):
  match ch:
    case Chr{+uu}:
      eu = Equal.sym(U32, uu, kk, ueq(uu, kk, h))
      %eu : {Lex.classify.go(_) == Lex.COther{} : Lex.Class}
      hk

# an e or E is a word character
law oth_e:
  for +ch: Char
  for h: {Laws.is_e(ch) == True{} : Bool}
  {Lex.classify(ch) == Lex.COther{} : Lex.Class}

def oth_e(ch, h):
  cls_by(ch, xx => V.num.ok.expmark(xx), h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a true `when`, by its condition
law when_el:
  for cc: Bool
  for +yy: Bool
  for +nn: Bool
  for pp: Type
  for h: {Laws.when(cc, yy, nn) == True{} : Bool}
  for kt: {cc == True{} : Bool} -> {yy == True{} : Bool} -> pp
  for kf: {nn == True{} : Bool} -> pp
  pp

def when_el(cc, _yy, _nn, _pp, h, kt, kf):
  match cc:
    case True{}:
      kt({==}, h)
    case False{}:
      kf(h)

# False is never True, at any type
law no:
  for pp: Type
  for h: {False{} == True{} : Bool}
  pp

def no(pp, h):
  Empty.absurd(pp, false_true(h))

# *DIGIT: word characters
law oth_digits_end:
  for +cs: List<&2, Char>
  for h: {Laws.digits_end(cs) == True{} : Bool}
  others(cs)

def oth_digits_end(cs, h):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+hd, +tl}:
      when_el(Laws.digit(hd), Laws.digits_end(tl), False{}, others(hd <> tl), h,
        ed => et => (oth_digit(hd, ed), oth_digits_end(tl, et)), ef => no(others(hd <> tl), ef))

# 1*DIGIT: word characters
law oth_digits1_end:
  for +cs: List<&2, Char>
  for h: {Laws.digits1_end(cs) == True{} : Bool}
  others(cs)

def oth_digits1_end(cs, h):
  match cs:
    case Nil{}:
      no(others([]), h)
    case Con{+hd, +tl}:
      when_el(Laws.digit(hd), Laws.digits_end(tl), False{}, others(hd <> tl), h,
        ed => et => (oth_digit(hd, ed), oth_digits_end(tl, et)), ef => no(others(hd <> tl), ef))

# an exponent's body: word characters
law oth_exp_body:
  for +cs: List<&2, Char>
  for h: {Laws.exp_body(cs) == True{} : Bool}
  others(cs)

def oth_exp_body(cs, h):
  match cs:
    case Nil{}:
      no(others([]), h)
    case Con{+hd, +tl}:
      when_el(Laws.is_cp(hd, 43), Laws.digits1_end(tl), Laws.when(Laws.is_cp(hd, 45), Laws.digits1_end(tl),
        Laws.when(Laws.digit(hd), Laws.digits_end(tl), False{})), others(hd <> tl), h,
        ec => et => (oth_cp(hd, 43, ec, {==}), oth_digits1_end(tl, et)),
        h2 => when_el(Laws.is_cp(hd, 45), Laws.digits1_end(tl), Laws.when(Laws.digit(hd), Laws.digits_end(tl),
          False{}), others(hd <> tl), h2,
          ec => et => (oth_cp(hd, 45, ec, {==}), oth_digits1_end(tl, et)),
          h3 => when_el(Laws.digit(hd), Laws.digits_end(tl), False{}, others(hd <> tl), h3,
            ed => et => (oth_digit(hd, ed), oth_digits_end(tl, et)), ef => no(others(hd <> tl), ef))))

# frac's other digits, then an exponent: word characters
law oth_digits_exp_end:
  for +cs: List<&2, Char>
  for h: {Laws.digits_exp_end(cs) == True{} : Bool}
  others(cs)

def oth_digits_exp_end(cs, h):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+hd, +tl}:
      when_el(Laws.digit(hd), Laws.digits_exp_end(tl), Laws.when(Laws.is_e(hd), Laws.exp_body(tl), False{}),
        others(hd <> tl), h,
        ed => et => (oth_digit(hd, ed), oth_digits_exp_end(tl, et)),
        h2 => when_el(Laws.is_e(hd), Laws.exp_body(tl), False{}, others(hd <> tl), h2,
          ee => et => (oth_e(hd, ee), oth_exp_body(tl, et)), ef => no(others(hd <> tl), ef)))

# frac's body: word characters
law oth_frac_body:
  for +cs: List<&2, Char>
  for h: {Laws.frac_body(cs) == True{} : Bool}
  others(cs)

def oth_frac_body(cs, h):
  match cs:
    case Nil{}:
      no(others([]), h)
    case Con{+hd, +tl}:
      when_el(Laws.digit(hd), Laws.digits_exp_end(tl), False{}, others(hd <> tl), h,
        ed => et => (oth_digit(hd, ed), oth_digits_exp_end(tl, et)), ef => no(others(hd <> tl), ef))

# after an int of 0: word characters
law oth_zero_rest:
  for +cs: List<&2, Char>
  for h: {Laws.zero_rest(cs) == True{} : Bool}
  others(cs)

def oth_zero_rest(cs, h):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+hd, +tl}:
      when_el(Laws.digit(hd), False{}, Laws.when(Laws.is_cp(hd, 46), Laws.frac_body(tl), Laws.when(Laws.is_e(hd),
        Laws.exp_body(tl), False{})), others(hd <> tl), h,
        _ed => ef => no(others(hd <> tl), ef),
        h2 => when_el(Laws.is_cp(hd, 46), Laws.frac_body(tl), Laws.when(Laws.is_e(hd), Laws.exp_body(tl), False{}),
          others(hd <> tl), h2,
          ec => et => (oth_cp(hd, 46, ec, {==}), oth_frac_body(tl, et)),
          h3 => when_el(Laws.is_e(hd), Laws.exp_body(tl), False{}, others(hd <> tl), h3,
            ee => et => (oth_e(hd, ee), oth_exp_body(tl, et)), ef => no(others(hd <> tl), ef))))

# after digit1-9: word characters
law oth_digits_rest:
  for +cs: List<&2, Char>
  for h: {Laws.digits_rest(cs) == True{} : Bool}
  others(cs)

def oth_digits_rest(cs, h):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+hd, +tl}:
      when_el(Laws.digit(hd), Laws.digits_rest(tl), Laws.when(Laws.is_cp(hd, 46), Laws.frac_body(tl),
        Laws.when(Laws.is_e(hd), Laws.exp_body(tl), False{})), others(hd <> tl), h,
        ed => et => (oth_digit(hd, ed), oth_digits_rest(tl, et)),
        h2 => when_el(Laws.is_cp(hd, 46), Laws.frac_body(tl), Laws.when(Laws.is_e(hd), Laws.exp_body(tl), False{}),
          others(hd <> tl), h2,
          ec => et => (oth_cp(hd, 46, ec, {==}), oth_frac_body(tl, et)),
          h3 => when_el(Laws.is_e(hd), Laws.exp_body(tl), False{}, others(hd <> tl), h3,
            ee => et => (oth_e(hd, ee), oth_exp_body(tl, et)), ef => no(others(hd <> tl), ef))))

# int, then frac and exp: word characters
law oth_int_end:
  for +cs: List<&2, Char>
  for h: {Laws.int_end(cs) == True{} : Bool}
  others(cs)

def oth_int_end(cs, h):
  match cs:
    case Nil{}:
      no(others([]), h)
    case Con{+hd, +tl}:
      when_el(Laws.is_cp(hd, 48), Laws.zero_rest(tl), Laws.when(Laws.digit19(hd), Laws.digits_rest(tl), False{}),
        others(hd <> tl),
        h,
        ec => et => (oth_cp(hd, 48, ec, {==}), oth_zero_rest(tl, et)),
        h2 => when_el(Laws.digit19(hd), Laws.digits_rest(tl), False{}, others(hd <> tl), h2,
          ed => et => (oth_digit19(hd, ed), oth_digits_rest(tl, et)), ef => no(others(hd <> tl), ef)))

# a JSON number: word characters
law oth_number:
  for +cs: List<&2, Char>
  for h: {Laws.number(cs) == True{} : Bool}
  others(cs)

def oth_number(cs, h):
  match cs:
    case Nil{}:
      no(others([]), h)
    case Con{+hd, +tl}:
      when_el(Laws.is_cp(hd, 45), Laws.int_end(tl), Laws.int_end(hd <> tl), others(hd <> tl), h,
        ec => et => (oth_cp(hd, 45, ec, {==}), oth_int_end(tl, et)),
        ei => oth_int_end(hd <> tl, ei))

# a word's characters, fed in Word mode, are pushed onto the buffer
law run_word:
  for +cs: List<&2, Char>
  for hw: others(cs)
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {Lex.run(cs, Lex.Lex{Lex.Word{}, buf, toks}) ==
    Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, cs, buf), toks} : Lex.Lex}

def run_word(cs, hw, buf, toks):
  match cs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      (hc, ht) = hw
      Equal.trans(Lex.Lex, Lex.run(tl, Lex.feed(hd, Lex.Lex{Lex.Word{}, buf, toks})),
        Lex.run(tl, Lex.Lex{Lex.Word{}, hd <> buf, toks}), Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, tl,
          hd <> buf), toks},
        Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(tl, xx), Lex.feed(hd, Lex.Lex{Lex.Word{}, buf, toks}),
          Lex.Lex{Lex.Word{}, hd <> buf, toks}, feed_as(hd, Lex.Word{}, buf, toks, Lex.COther{}, hc)),
        run_word(tl, ht, hd <> buf, toks))

# a string's characters, listed then gathered, are the string
law from_to:
  for +txt: String
  {String.from_list(String.to_list(txt)) == txt : String}

def from_to(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{hd, tl}:
      Equal.cong(String, String, xx => SCon{hd, xx}, String.from_list(String.to_list(tl)), tl, from_to(tl))

# a buffer of reversed characters, read back
law text_revgo:
  for +cs: List<&2, Char>
  for +buf: List<&2, Char>
  for +acc: String
  {Lex.text.go(List.reverse.go(&2, Char, cs, buf), acc) == Lex.text.go(buf, String.from_list(cs) ++ acc) : String}

def text_revgo(cs, buf, acc):
  match cs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      text_revgo(tl, hd <> buf, acc)

# a word's buffer reads back as the word
law word_text:
  for +raw: String
  {Lex.text(List.reverse.go(&2, Char, String.to_list(raw), [])) == raw : String}

def word_text(raw):
  +fl = String.from_list(String.to_list(raw))
  Equal.trans(String, Lex.text.go(List.reverse.go(&2, Char, String.to_list(raw), []), ""), fl ++ "", raw,
    text_revgo(String.to_list(raw), [], ""),
    Equal.trans(String, fl ++ "", fl, raw, append_nil(fl), from_to(raw)))

# word characters, from between tokens, make a word
law lex_word:
  for +hd: Char
  for +tl: List<&2, Char>
  for hw: others(hd <> tl)
  for +toks: List<&2, Lex.Tok>
  {Lex.run(hd <> tl, Lex.Lex{Lex.Idle{}, [], toks}) ==
    Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, hd <> tl, []), toks} : Lex.Lex}

def lex_word(hd, tl, hw, toks):
  (hc, ht) = hw
  Equal.trans(Lex.Lex, Lex.run(tl, Lex.feed(hd, Lex.Lex{Lex.Idle{}, [], toks})),
    Lex.run(tl, Lex.Lex{Lex.Word{}, [hd], toks}), Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, tl, [hd]), toks},
    Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(tl, xx), Lex.feed(hd, Lex.Lex{Lex.Idle{}, [], toks}),
      Lex.Lex{Lex.Word{}, [hd], toks}, feed_as(hd, Lex.Idle{}, [], toks, Lex.COther{}, hc)),
    run_word(tl, ht, [hd], toks))

# a JSON number's characters, from between tokens, make a word
law lex_numl:
  for +cs: List<&2, Char>
  for hn: {Laws.number(cs) == True{} : Bool}
  for +toks: List<&2, Lex.Tok>
  {Lex.run(cs, Lex.Lex{Lex.Idle{}, [], toks}) == Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, cs, []), toks} : Lex.Lex}

def lex_numl(cs, hn, toks):
  match cs:
    case Nil{}:
      no({Lex.run([], Lex.Lex{Lex.Idle{}, [], toks}) == Lex.Lex{Lex.Word{}, [], toks} : Lex.Lex}, hn)
    case Con{+hd, +tl}:
      lex_word(hd, tl, oth_number(hd <> tl, hn), toks)

# reversing onto an accumulator goes through an append
law rev_app:
  for +aa: List<&2, Lex.Tok>
  for +bb: List<&2, Lex.Tok>
  for +acc: List<&2, Lex.Tok>
  {List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, aa, bb), acc) ==
    List.reverse.go(&2, Lex.Tok, bb, List.reverse.go(&2, Lex.Tok, aa, acc)) : List<&2, Lex.Tok>}

def rev_app(aa, bb, acc):
  match aa:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      rev_app(tl, bb, hd <> acc)

# reversing twice gives back the list
law rev_rev:
  for +xs: List<&2, Lex.Tok>
  for +acc: List<&2, Lex.Tok>
  for +ys: List<&2, Lex.Tok>
  {List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, xs, acc), ys) ==
    List.reverse.go(&2, Lex.Tok, acc, List.append(&2, Lex.Tok, xs, ys)) : List<&2, Lex.Tok>}

def rev_rev(xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      rev_rev(tl, hd <> acc, ys)

# the lexer on two strings, where the first leads to a known state
law seq:
  for +aa: String
  for +bb: String
  for +st: Lex.Lex
  for +mid: Lex.Lex
  for e1: {Lex.run(String.to_list(aa), st) == mid : Lex.Lex}
  {Lex.run(String.to_list(aa ++ bb), st) == Lex.run(String.to_list(bb), mid) : Lex.Lex}

def seq(aa, bb, st, mid, e1):
  Equal.trans(Lex.Lex, Lex.run(String.to_list(aa ++ bb), st), Lex.run(String.to_list(bb), Lex.run(String.to_list(aa),
    st)),
    Lex.run(String.to_list(bb), mid), run_app(aa, bb, st),
    Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list(bb), xx), Lex.run(String.to_list(aa), st), mid, e1))

# the tokens a value is, read straight off it: by shape, a value, an array's
# cells, or an object's cells. Strings are fixed as print writes them
def tj(val: V.Json, sh: V.Shape) -> List<&2, Lex.Tok>:
  match val sh:
    case V.JNull{} V.WVal{}:
      [Lex.TWord{"null"}]
    case V.JBool{True{}} V.WVal{}:
      [Lex.TWord{"true"}]
    case V.JBool{False{}} V.WVal{}:
      [Lex.TWord{"false"}]
    case V.JNum{raw} V.WVal{}:
      [Lex.TWord{raw}]
    case V.JStr{txt} V.WVal{}:
      [Lex.TStr{fixs(String.to_list(txt))}]
    case V.JSpan{src, +nn} V.WVal{}:
      [Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))}]
    case V.JArr{items} V.WVal{}:
      Lex.TOpenArr{} <> List.append(&2, Lex.Tok, tj(items, V.WArr{}), [Lex.TCloseArr{}])
    case V.JObj{pairs} V.WVal{}:
      Lex.TOpenObj{} <> List.append(&2, Lex.Tok, tj(pairs, V.WObj{}), [Lex.TCloseObj{}])
    case V.JNil{} V.WArr{}:
      []
    case V.JCons{hd, V.JNil{}} V.WArr{}:
      tj(hd, V.WVal{})
    case V.JCons{hd, tl} V.WArr{}:
      List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(tl, V.WArr{}))
    case V.JNil{} V.WObj{}:
      []
    case V.JPair{kk, vv, V.JNil{}} V.WObj{}:
      Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> tj(vv, V.WVal{})
    case V.JPair{kk, vv, rr} V.WObj{}:
      Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <>
        List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(rr, V.WObj{}))
    case V.JBind{src, +nn, vv, V.JNil{}} V.WObj{}:
      Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> Lex.TColon{} <> tj(vv, V.WVal{})
    case V.JBind{src, +nn, vv, rr} V.WObj{}:
      Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> Lex.TColon{} <>
        List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(rr, V.WObj{}))
    case _ _:
      []

# the character lexer's state after a value's text, from between tokens: a
# word still open, or the value's tokens pushed
def pend(val: V.Json, acc: List<&2, Lex.Tok>) -> Lex.Lex:
  match val:
    case V.JNull{}:
      Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, String.to_list("null"), []), acc}
    case V.JBool{bb}:
      match bb:
        case True{}:
          Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, String.to_list("true"), []), acc}
        case False{}:
          Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, String.to_list("false"), []), acc}
    case V.JNum{raw}:
      Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, String.to_list(raw), []), acc}
    case V.JStr{a1}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JStr{a1}, V.WVal{}), acc)}
    case V.JArr{a1}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JArr{a1}, V.WVal{}), acc)}
    case V.JObj{a1}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JObj{a1}, V.WVal{}), acc)}
    case V.JNil{}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JNil{}, V.WVal{}), acc)}
    case V.JCons{a1, a2}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JCons{a1, a2}, V.WVal{}), acc)}
    case V.JPair{a1, a2, a3}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JPair{a1, a2, a3}, V.WVal{}), acc)}
    case V.JSpan{a1, a2}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JSpan{a1, a2}, V.WVal{}), acc)}
    case V.JBind{a1, a2, a3, a4}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JBind{a1, a2, a3, a4}, V.WVal{}), acc)}

# a punctuation character after a value's text pushes its tokens, then its own
law close:
  for +val: V.Json
  for +ch: Char
  for +tt: Lex.Tok
  for ec: {Lex.classify(ch) == Lex.CPunct{tt} : Lex.Class}
  for +acc: List<&2, Lex.Tok>
  {Lex.feed(ch, pend(val, acc)) ==
    Lex.Lex{Lex.Idle{}, [], tt <> List.reverse.go(&2, Lex.Tok, tj(val, V.WVal{}), acc)} : Lex.Lex}

def close(val, ch, tt, ec, acc):
  match val:
    case V.JNull{}:
      feed_as(ch, Lex.Word{}, List.reverse.go(&2, Char, String.to_list("null"), []), acc, Lex.CPunct{tt}, ec)
    case V.JBool{bb}:
      match bb:
        case True{}:
          feed_as(ch, Lex.Word{}, List.reverse.go(&2, Char, String.to_list("true"), []), acc, Lex.CPunct{tt}, ec)
        case False{}:
          feed_as(ch, Lex.Word{}, List.reverse.go(&2, Char, String.to_list("false"), []), acc, Lex.CPunct{tt}, ec)
    case V.JNum{+raw}:
      +bf = List.reverse.go(&2, Char, String.to_list(raw), [])
      Equal.trans(Lex.Lex, Lex.feed(ch, Lex.Lex{Lex.Word{}, bf, acc}),
        Lex.Lex{Lex.Idle{}, [], tt <> Lex.TWord{Lex.text(bf)} <> acc},
        Lex.Lex{Lex.Idle{}, [], tt <> Lex.TWord{raw} <> acc},
        feed_as(ch, Lex.Word{}, bf, acc, Lex.CPunct{tt}, ec),
        Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], tt <> Lex.TWord{xx} <> acc}, Lex.text(bf), raw,
          word_text(raw)))
    case V.JStr{a1}:
      feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JStr{a1}, V.WVal{}), acc), Lex.CPunct{tt}, ec)
    case V.JArr{a1}:
      feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JArr{a1}, V.WVal{}), acc), Lex.CPunct{tt}, ec)
    case V.JObj{a1}:
      feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JObj{a1}, V.WVal{}), acc), Lex.CPunct{tt}, ec)
    case V.JNil{}:
      feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JNil{}, V.WVal{}), acc), Lex.CPunct{tt}, ec)
    case V.JCons{a1, a2}:
      feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JCons{a1, a2}, V.WVal{}), acc), Lex.CPunct{tt}, ec)
    case V.JPair{a1, a2, a3}:
      feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JPair{a1, a2, a3}, V.WVal{}), acc), Lex.CPunct{tt},
        ec)
    case V.JSpan{a1, a2}:
      feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JSpan{a1, a2}, V.WVal{}), acc), Lex.CPunct{tt}, ec)
    case V.JBind{a1, a2, a3, a4}:
      feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, tj(V.JBind{a1, a2, a3, a4}, V.WVal{}), acc),
        Lex.CPunct{tt}, ec)

# a true early exit: its test held
law stop_l:
  for aa: Bool
  for -bb: Bool
  for h: {Lazy.stop(Bool, Bool.not(aa), False{}, _u => bb) == True{} : Bool}
  {aa == True{} : Bool}

def stop_l(aa, _bb, h):
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(h))

# a true early exit: the rest held
law stop_r:
  for aa: Bool
  for -bb: Bool
  for h: {Lazy.stop(Bool, Bool.not(aa), False{}, _u => bb) == True{} : Bool}
  {bb == True{} : Bool}

def stop_r(aa, bb, h):
  match aa:
    case True{}:
      h
    case False{}:
      Empty.absurd({bb == True{} : Bool}, false_true(h))






# what lexp says of a value by its shape: a value's text leads to pend; an
# array's or object's cells, then the closing bracket, push their tokens
def lg(+val: V.Json, sh: V.Shape, +acc: List<&2, Lex.Tok>) -> Type:
  match sh:
    case V.WVal{}:
      {Lex.run(String.to_list(Print.print(val)), Lex.Lex{Lex.Idle{}, [], acc}) == pend(val, acc) : Lex.Lex}
    case V.WArr{}:
      {Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(val)), Lex.Lex{Lex.Idle{}, [], acc})) ==
        Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(val, V.WArr{}), acc)} : Lex.Lex}
    case V.WObj{}:
      {Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(val)), Lex.Lex{Lex.Idle{}, [], acc})) ==
        Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(val, V.WObj{}), acc)} : Lex.Lex}

# lexp for a boolean
law lexp_bool:
  for bb: Bool
  for +acc: List<&2, Lex.Tok>
  lg(V.JBool{bb}, V.WVal{}, acc)

def lexp_bool(bb, _acc):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# lexp for an array cell, by what follows it
law lexp_cons:
  for tl: V.Json
  for +hd: V.Json
  for +h: {V.wf.go(V.JCons{hd, tl}, V.WArr{}) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  for ih_hd: {V.wf.go(hd, V.WVal{}) == True{} : Bool} -> lg(hd, V.WVal{}, acc)
  for ih_tl: {V.wf.go(tl, V.WArr{}) == True{} : Bool} -> lg(tl, V.WArr{}, Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
    tj(hd, V.WVal{}), acc))
  lg(V.JCons{hd, tl}, V.WArr{}, acc)

def lexp_cons(tl, hd, h, acc, ih_hd, ih_tl):
  match tl:
    case V.JNil{}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNil{}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(hd)), Lex.Lex{Lex.Idle{},
        [], acc})), Lex.run(String.to_list("]"), pend(hd, acc)), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}, Equal.cong(Lex.Lex, Lex.Lex,
          xx => Lex.run(String.to_list("]"), xx), Lex.run(String.to_list(Print.print(hd)), Lex.Lex{Lex.Idle{}, [],
          acc}), pend(hd, acc), ih_hd(hd_ok)), close(hd, ']', Lex.TCloseArr{}, {==}, acc))
    case V.JNull{}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNull{}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNull{}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JNull{}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNull{})), pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), seq(Print.print(hd), "," ++ Print.print(V.JNull{}), Lex.Lex{Lex.Idle{},
          [], acc}, pend(hd, acc), ih_hd(hd_ok)), seq(",", Print.print(V.JNull{}), pend(hd, acc), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}, close(hd, ',', Lex.TComma{}, {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JNull{})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JNull{}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JNull{}}, V.WArr{}), acc)}, ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd,
          V.JNull{}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JNull{}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JNull{},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, tj(V.JNull{}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)), rev_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JNull{}, V.WArr{}), acc)))))
    case V.JBool{+t1}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBool{t1}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBool{t1}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JBool{t1}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JBool{t1})), pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), seq(Print.print(hd), "," ++ Print.print(V.JBool{t1}), Lex.Lex{Lex.Idle{},
          [], acc}, pend(hd, acc), ih_hd(hd_ok)), seq(",", Print.print(V.JBool{t1}), pend(hd, acc), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}, close(hd, ',', Lex.TComma{}, {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JBool{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JBool{t1}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JBool{t1}}, V.WArr{}), acc)}, ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd,
          V.JBool{t1}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JBool{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JBool{t1},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, tj(V.JBool{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)), rev_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JBool{t1}, V.WArr{}),
          acc)))))
    case V.JNum{+t1}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNum{t1}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNum{t1}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JNum{t1}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNum{t1})), pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), seq(Print.print(hd), "," ++ Print.print(V.JNum{t1}), Lex.Lex{Lex.Idle{},
          [], acc}, pend(hd, acc), ih_hd(hd_ok)), seq(",", Print.print(V.JNum{t1}), pend(hd, acc), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}, close(hd, ',', Lex.TComma{}, {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JNum{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JNum{t1}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JNum{t1}}, V.WArr{}), acc)}, ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd,
          V.JNum{t1}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JNum{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JNum{t1},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, tj(V.JNum{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)), rev_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JNum{t1}, V.WArr{}), acc)))))
    case V.JStr{+t1}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JStr{t1}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JStr{t1}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JStr{t1}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JStr{t1})), pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), seq(Print.print(hd), "," ++ Print.print(V.JStr{t1}), Lex.Lex{Lex.Idle{},
          [], acc}, pend(hd, acc), ih_hd(hd_ok)), seq(",", Print.print(V.JStr{t1}), pend(hd, acc), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}, close(hd, ',', Lex.TComma{}, {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JStr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JStr{t1}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JStr{t1}}, V.WArr{}), acc)}, ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd,
          V.JStr{t1}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JStr{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JStr{t1},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, tj(V.JStr{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)), rev_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JStr{t1}, V.WArr{}), acc)))))
    case V.JArr{+t1}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JArr{t1}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JArr{t1}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JArr{t1}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JArr{t1})), pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), seq(Print.print(hd), "," ++ Print.print(V.JArr{t1}), Lex.Lex{Lex.Idle{},
          [], acc}, pend(hd, acc), ih_hd(hd_ok)), seq(",", Print.print(V.JArr{t1}), pend(hd, acc), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}, close(hd, ',', Lex.TComma{}, {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JArr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JArr{t1}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JArr{t1}}, V.WArr{}), acc)}, ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd,
          V.JArr{t1}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JArr{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JArr{t1},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, tj(V.JArr{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)), rev_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JArr{t1}, V.WArr{}), acc)))))
    case V.JObj{+t1}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JObj{t1}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JObj{t1}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JObj{t1}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JObj{t1})), pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}), seq(Print.print(hd), "," ++ Print.print(V.JObj{t1}), Lex.Lex{Lex.Idle{},
          [], acc}, pend(hd, acc), ih_hd(hd_ok)), seq(",", Print.print(V.JObj{t1}), pend(hd, acc), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}, close(hd, ',', Lex.TComma{}, {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JObj{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JObj{t1}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JObj{t1}}, V.WArr{}), acc)}, ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd,
          V.JObj{t1}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JObj{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JObj{t1},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, tj(V.JObj{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)), rev_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JObj{t1}, V.WArr{}), acc)))))
    case V.JCons{+t1, +t2}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JCons{t1,
        t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JCons{t1, t2}},
          V.WArr{}), acc)}, Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}), seq(Print.print(hd),
          "," ++ Print.print(V.JCons{t1, t2}), Lex.Lex{Lex.Idle{}, [], acc}, pend(hd, acc), ih_hd(hd_ok)), seq(",",
          Print.print(V.JCons{t1, t2}), pend(hd, acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}, close(hd, ',', Lex.TComma{}, {==}, acc)))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{t1, t2}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JCons{t1, t2}}, V.WArr{}), acc)},
          ih_tl(tl_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JCons{hd, V.JCons{t1, t2}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{t1, t2}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WArr{})), acc), List.reverse.go(&2, Lex.Tok,
          tj(V.JCons{t1, t2}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)),
          rev_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WArr{}), acc)))))
    case V.JPair{+t1, +t2, +t3}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JPair{t1, t2,
        t3})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JPair{t1, t2, t3}},
          V.WArr{}), acc)}, Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}), seq(Print.print(hd),
          "," ++ Print.print(V.JPair{t1, t2, t3}), Lex.Lex{Lex.Idle{}, [], acc}, pend(hd, acc), ih_hd(hd_ok)), seq(",",
          Print.print(V.JPair{t1, t2, t3}), pend(hd, acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}, close(hd, ',', Lex.TComma{}, {==}, acc)))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JPair{t1, t2, t3}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JPair{t1, t2, t3}}, V.WArr{}), acc)},
          ih_tl(tl_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JCons{hd, V.JPair{t1, t2, t3}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JPair{t1, t2, t3}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WArr{})), acc), List.reverse.go(&2, Lex.Tok,
          tj(V.JPair{t1, t2, t3}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)),
          rev_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WArr{}), acc)))))
    case V.JSpan{+t1, +t2}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JSpan{t1,
        t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JSpan{t1, t2}},
          V.WArr{}), acc)}, Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}), seq(Print.print(hd),
          "," ++ Print.print(V.JSpan{t1, t2}), Lex.Lex{Lex.Idle{}, [], acc}, pend(hd, acc), ih_hd(hd_ok)), seq(",",
          Print.print(V.JSpan{t1, t2}), pend(hd, acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(hd, V.WVal{}), acc)}, close(hd, ',', Lex.TComma{}, {==}, acc)))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JSpan{t1, t2}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JSpan{t1, t2}}, V.WArr{}), acc)},
          ih_tl(tl_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JCons{hd, V.JSpan{t1, t2}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JSpan{t1, t2}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WArr{})), acc), List.reverse.go(&2, Lex.Tok,
          tj(V.JSpan{t1, t2}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)),
          rev_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WArr{}), acc)))))
    case V.JBind{+t1, +t2, +t3, +t4}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
        [], acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3,
        t4})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JBind{t1, t2, t3,
          t4}}, V.WArr{}), acc)}, Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
          [], acc}), Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
          [], acc}), Lex.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})), pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}), seq(Print.print(hd),
          "," ++ Print.print(V.JBind{t1, t2, t3, t4}), Lex.Lex{Lex.Idle{}, [], acc}, pend(hd, acc), ih_hd(hd_ok)),
          seq(",", Print.print(V.JBind{t1, t2, t3, t4}), pend(hd, acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)}, close(hd, ',', Lex.TComma{}, {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JBind{t1, t2,
          t3, t4})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JBind{t1, t2, t3, t4},
          V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{hd, V.JBind{t1, t2, t3, t4}}, V.WArr{}), acc)},
          ih_tl(tl_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JCons{hd, V.JBind{t1, t2, t3, t4}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(V.JBind{t1, t2, t3, t4}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WArr{})), acc), List.reverse.go(&2, Lex.Tok,
          tj(V.JBind{t1, t2, t3, t4}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)),
          rev_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WArr{}), acc)))))

# lexp for an object cell, by what follows it
law lexp_pair:
  for rr: V.Json
  for +kk: String
  for +vv: V.Json
  for +h: {V.wf.go(V.JPair{kk, vv, rr}, V.WObj{}) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  for ih_v: {V.wf.go(vv, V.WVal{}) == True{} : Bool} -> lg(vv, V.WVal{},
    Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)
  for ih_r: {V.wf.go(rr, V.WObj{}) == True{} : Bool} -> lg(rr, V.WObj{}, Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
    tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))
  lg(V.JPair{kk, vv, rr}, V.WObj{}, acc)

def lexp_pair(rr, kk, vv, h, acc, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ Print.print(vv))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Equal.cong(Lex.Lex, Lex.Lex,
          xx => Lex.run(String.to_list("}"), xx), Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ Print.print(vv))),
          Lex.Lex{Lex.Idle{}, [], acc}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ Print.print(vv))), Lex.Lex{Lex.Idle{},
          [], acc}), Lex.run(String.to_list(":" ++ Print.print(vv)), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), seq(Print.quote(kk), ":" ++ Print.print(vv),
          Lex.Lex{Lex.Idle{}, [], acc}, Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc},
          lex_quote(kk, acc)), Equal.trans(Lex.Lex, Lex.run(String.to_list(":" ++ Print.print(vv)), Lex.Lex{Lex.Idle{},
          [], Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(vv)), Lex.Lex{Lex.Idle{},
          [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), seq(":", Print.print(vv), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, {==}), ih_v(v_ok)))), close(vv, '}',
          Lex.TCloseObj{}, {==}, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))
    case V.JNull{}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JNull{}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JNull{})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JNull{})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNull{})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JNull{})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.print(vv),
          "," ++ Print.print(V.JNull{}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), seq(",", Print.print(V.JNull{}),
          pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JNull{}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{},
          [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JNull{}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNull{}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JNull{}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2,
          Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNull{}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JNull{},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), rev_app(tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JNull{}, V.WObj{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))
    case V.JBool{+t1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))), Lex.Lex{Lex.Idle{},
          [], Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JBool{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))), Lex.Lex{Lex.Idle{},
          [], Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JBool{t1})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.print(vv),
          "," ++ Print.print(V.JBool{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), seq(",", Print.print(V.JBool{t1}),
          pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JBool{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JBool{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JBool{t1},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), rev_app(tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))
    case V.JNum{+t1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JNum{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JNum{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNum{t1})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JNum{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.print(vv),
          "," ++ Print.print(V.JNum{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), seq(",", Print.print(V.JNum{t1}),
          pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JNum{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{},
          [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JNum{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2,
          Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JNum{t1},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), rev_app(tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))
    case V.JStr{+t1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JStr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JStr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JStr{t1})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JStr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.print(vv),
          "," ++ Print.print(V.JStr{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), seq(",", Print.print(V.JStr{t1}),
          pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JStr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{},
          [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JStr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2,
          Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JStr{t1},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), rev_app(tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))
    case V.JArr{+t1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JArr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JArr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JArr{t1})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JArr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.print(vv),
          "," ++ Print.print(V.JArr{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), seq(",", Print.print(V.JArr{t1}),
          pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JArr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{},
          [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JArr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2,
          Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JArr{t1},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), rev_app(tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))
    case V.JObj{+t1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JObj{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JObj{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JObj{t1})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JObj{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.print(vv),
          "," ++ Print.print(V.JObj{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), seq(",", Print.print(V.JObj{t1}),
          pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JObj{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{},
          [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JObj{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2,
          Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JObj{t1},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), rev_app(tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))
    case V.JCons{+t1, +t2}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))))),
        Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JCons{t1,
        t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1,
          t2}))))), Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JCons{t1, t2})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1,
          t2}))))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JCons{t1,
          t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JCons{t1,
          t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.print(vv),
          "," ++ Print.print(V.JCons{t1, t2}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), seq(",", Print.print(V.JCons{t1,
          t2}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JCons{t1, t2},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), rev_app(tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))
    case V.JPair{+t1, +t2, +t3}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
        t3}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Equal.cong(Lex.Lex, Lex.Lex,
          xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
          t3}))))), Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
          t3}))))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JPair{t1,
          t2, t3})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JPair{t1,
          t2, t3})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.print(vv),
          "," ++ Print.print(V.JPair{t1, t2, t3}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), seq(",", Print.print(V.JPair{t1, t2,
          t3}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, ih_r(r_ok), Equal.sym(Lex.Lex,
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JPair{t1, t2,
          t3}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), rev_app(tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))
    case V.JSpan{+t1, +t2}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))))),
        Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JSpan{t1,
        t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1,
          t2}))))), Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1,
          t2}))))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JSpan{t1,
          t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JSpan{t1,
          t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.print(vv),
          "," ++ Print.print(V.JSpan{t1, t2}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), seq(",", Print.print(V.JSpan{t1,
          t2}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JSpan{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JSpan{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JSpan{t1, t2},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), rev_app(tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))
    case V.JBind{+t1, +t2, +t3, +t4}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
        t4}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Equal.cong(Lex.Lex, Lex.Lex,
          xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
          t4}))))), Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
          t4}))))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
          [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
          [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JBind{t1,
          t2, t3, t4})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}), seq(Print.print(vv),
          "," ++ Print.print(V.JBind{t1, t2, t3, t4}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), seq(",", Print.print(V.JBind{t1, t2,
          t3, t4}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JBind{t1, t2, t3, t4}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, ih_r(r_ok), Equal.sym(Lex.Lex,
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JBind{t1, t2, t3, t4}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JBind{t1, t2,
          t3, t4}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)), rev_app(tj(vv, V.WVal{}),
          Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))))

# lexp for an object cell with a span key, by what follows it
law lexp_bind:
  for rr: V.Json
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for +h: {V.wf.go(V.JBind{src, nn, vv, rr}, V.WObj{}) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  for ih_v: {V.wf.go(vv, V.WVal{}) == True{} : Bool} -> lg(vv, V.WVal{},
    Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)
  for ih_r: {V.wf.go(rr, V.WObj{}) == True{} : Bool} -> lg(rr, V.WObj{}, Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
    tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))
  lg(V.JBind{src, nn, vv, rr}, V.WObj{}, acc)

def lexp_bind(rr, src, nn, vv, h, acc, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ Print.print(vv))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ (":" ++ Print.print(vv))),
          Lex.Lex{Lex.Idle{}, [], acc}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ Print.print(vv))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ Print.print(vv)), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))), ":" ++ Print.print(vv), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ Print.print(vv)), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv)), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), seq(":",
          Print.print(vv), Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, {==}),
          ih_v(v_ok)))), close(vv, '}', Lex.TCloseObj{}, {==},
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))
    case V.JNull{}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JNull{}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JNull{})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNull{})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.print(vv), "," ++ Print.print(V.JNull{}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          seq(",", Print.print(V.JNull{}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JNull{}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JNull{}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNull{}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JNull{}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNull{},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, tj(V.JNull{}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          rev_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNull{}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JBool{+t1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))), Lex.Lex{Lex.Idle{},
          [], acc}), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))), Lex.Lex{Lex.Idle{},
          [], acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))), Lex.Lex{Lex.Idle{},
          [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JBool{t1})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.print(vv), "," ++ Print.print(V.JBool{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          seq(",", Print.print(V.JBool{t1}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JBool{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JBool{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBool{t1},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, tj(V.JBool{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          rev_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JNum{+t1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNum{t1})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.print(vv), "," ++ Print.print(V.JNum{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          seq(",", Print.print(V.JNum{t1}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JNum{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JNum{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNum{t1},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, tj(V.JNum{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          rev_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JStr{+t1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JStr{t1})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.print(vv), "," ++ Print.print(V.JStr{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          seq(",", Print.print(V.JStr{t1}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JStr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JStr{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JStr{t1},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, tj(V.JStr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          rev_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JArr{+t1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JArr{t1})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.print(vv), "," ++ Print.print(V.JArr{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          seq(",", Print.print(V.JArr{t1}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JArr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JArr{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JArr{t1},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, tj(V.JArr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          rev_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JObj{+t1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JObj{t1})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), seq(Print.print(vv), "," ++ Print.print(V.JObj{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          seq(",", Print.print(V.JObj{t1}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          tj(V.JObj{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JObj{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JObj{t1},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, tj(V.JObj{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          rev_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JCons{+t1, +t2}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1,
        t2}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, {==}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))),
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}), Lex.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          seq(Print.print(vv), "," ++ Print.print(V.JCons{t1, t2}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          seq(",", Print.print(V.JCons{t1, t2}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src,
          nn, U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JCons{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JCons{t1, t2},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, tj(V.JCons{t1, t2}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
          tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)), rev_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JPair{+t1, +t2, +t3}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
        t3}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, {==}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))),
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}), Lex.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          seq(Print.print(vv), "," ++ Print.print(V.JPair{t1, t2, t3}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          seq(",", Print.print(V.JPair{t1, t2, t3}), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, close(vv, ',',
          Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JPair{t1, t2,
          t3}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)), rev_app(tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JSpan{+t1, +t2}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1,
        t2}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, {==}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))),
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}), Lex.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          seq(Print.print(vv), "," ++ Print.print(V.JSpan{t1, t2}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          seq(",", Print.print(V.JSpan{t1, t2}), pend(vv, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src,
          nn, U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JSpan{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JSpan{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{t1, t2},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, tj(V.JSpan{t1, t2}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
          tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)), rev_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JBind{+t1, +t2, +t3, +t4}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
        t4}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
          [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}), seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, {==}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
          t4}))), Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}), Lex.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          seq(Print.print(vv), "," ++ Print.print(V.JBind{t1, t2, t3, t4}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          seq(",", Print.print(V.JBind{t1, t2, t3, t4}), pend(vv,
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, close(vv, ',',
          Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JBind{t1, t2, t3, t4},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(V.JBind{t1, t2, t3, t4},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBind{t1, t2,
          t3, t4}, V.WObj{})), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), List.reverse.go(&2, Lex.Tok, tj(V.JBind{t1, t2, t3, t4}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)), rev_app(tj(vv,
          V.WVal{}), Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))

# the character lexer on a well-formed value's text
law lexp:
  for +val: V.Json
  for +sh: V.Shape
  for +h: {V.wf.go(val, sh) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  lg(val, sh, acc)

def lexp(val, sh, h, acc):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          no(lg(V.JNull{}, V.WArr{}, acc), h)
        case V.WObj{}:
          no(lg(V.JNull{}, V.WObj{}, acc), h)
    case V.JBool{bb}:
      match sh:
        case V.WVal{}:
          lexp_bool(bb, acc)
        case V.WArr{}:
          no(lg(V.JBool{bb}, V.WArr{}, acc), h)
        case V.WObj{}:
          no(lg(V.JBool{bb}, V.WObj{}, acc), h)
    case V.JNum{+raw}:
      match sh:
        case V.WVal{}:
          lex_numl(String.to_list(raw), Equal.trans(Bool, Laws.number(String.to_list(raw)), V.num.ok(raw), True{},
            Equal.sym(Bool, V.num.ok(raw), Laws.number(String.to_list(raw)), Laws.num_grammar(raw)), h), acc)
        case V.WArr{}:
          no(lg(V.JNum{raw}, V.WArr{}, acc), h)
        case V.WObj{}:
          no(lg(V.JNum{raw}, V.WObj{}, acc), h)
    case V.JStr{+txt}:
      match sh:
        case V.WVal{}:
          lex_quote(txt, acc)
        case V.WArr{}:
          no(lg(V.JStr{txt}, V.WArr{}, acc), h)
        case V.WObj{}:
          no(lg(V.JStr{txt}, V.WObj{}, acc), h)
    case V.JArr{+items}:
      match sh:
        case V.WVal{}:
          Equal.trans(Lex.Lex, Lex.run(String.to_list("[" ++ (Print.print(items) ++ "]")), Lex.Lex{Lex.Idle{}, [],
            acc}), Lex.run(String.to_list(Print.print(items) ++ "]"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}),
              Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(items, V.WArr{}),
              [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, seq("[", Print.print(items) ++ "]", Lex.Lex{Lex.Idle{}, [],
              acc}, Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}, {==}), Equal.trans(Lex.Lex,
              Lex.run(String.to_list(Print.print(items) ++ "]"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}),
              Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(items)), Lex.Lex{Lex.Idle{}, [],
              Lex.TOpenArr{} <> acc})), Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
              tj(items, V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, run_app(Print.print(items), "]",
              Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
              Lex.run(String.to_list(Print.print(items)), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc})),
              Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(items, V.WArr{}),
              Lex.TOpenArr{} <> acc)}, Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
              tj(items, V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, lexp(items, V.WArr{}, h,
              Lex.TOpenArr{} <> acc), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok,
              List.append(&2, Lex.Tok, tj(items, V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)},
              Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(items, V.WArr{}),
              Lex.TOpenArr{} <> acc)}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], xx},
              List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(items, V.WArr{}), [Lex.TCloseArr{}]),
              Lex.TOpenArr{} <> acc), Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, tj(items, V.WArr{}),
              Lex.TOpenArr{} <> acc), rev_app(tj(items, V.WArr{}), [Lex.TCloseArr{}], Lex.TOpenArr{} <> acc))))))
        case V.WArr{}:
          no(lg(V.JArr{items}, V.WArr{}, acc), h)
        case V.WObj{}:
          no(lg(V.JArr{items}, V.WObj{}, acc), h)
    case V.JObj{+pairs}:
      match sh:
        case V.WVal{}:
          Equal.trans(Lex.Lex, Lex.run(String.to_list("{" ++ (Print.print(pairs) ++ "}")), Lex.Lex{Lex.Idle{}, [],
            acc}), Lex.run(String.to_list(Print.print(pairs) ++ "}"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}),
              Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(pairs, V.WObj{}),
              [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, seq("{", Print.print(pairs) ++ "}", Lex.Lex{Lex.Idle{}, [],
              acc}, Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}, {==}), Equal.trans(Lex.Lex,
              Lex.run(String.to_list(Print.print(pairs) ++ "}"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}),
              Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(pairs)), Lex.Lex{Lex.Idle{}, [],
              Lex.TOpenObj{} <> acc})), Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
              tj(pairs, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, run_app(Print.print(pairs), "}",
              Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
              Lex.run(String.to_list(Print.print(pairs)), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc})),
              Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(pairs, V.WObj{}),
              Lex.TOpenObj{} <> acc)}, Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
              tj(pairs, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, lexp(pairs, V.WObj{}, h,
              Lex.TOpenObj{} <> acc), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok,
              List.append(&2, Lex.Tok, tj(pairs, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)},
              Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(pairs, V.WObj{}),
              Lex.TOpenObj{} <> acc)}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], xx},
              List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, tj(pairs, V.WObj{}), [Lex.TCloseObj{}]),
              Lex.TOpenObj{} <> acc), Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, tj(pairs, V.WObj{}),
              Lex.TOpenObj{} <> acc), rev_app(tj(pairs, V.WObj{}), [Lex.TCloseObj{}], Lex.TOpenObj{} <> acc))))))
        case V.WArr{}:
          no(lg(V.JObj{pairs}, V.WArr{}, acc), h)
        case V.WObj{}:
          no(lg(V.JObj{pairs}, V.WObj{}, acc), h)
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          no(lg(V.JNil{}, V.WVal{}, acc), h)
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JCons{+hd, +tl}:
      match sh:
        case V.WVal{}:
          no(lg(V.JCons{hd, tl}, V.WVal{}, acc), h)
        case V.WArr{}:
          lexp_cons(tl, hd, h, acc, xx => lexp(hd, V.WVal{}, xx, acc), xx => lexp(tl, V.WArr{}, xx,
            Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(hd, V.WVal{}), acc)))
        case V.WObj{}:
          no(lg(V.JCons{hd, tl}, V.WObj{}, acc), h)
    case V.JPair{+kk, +vv, +rr}:
      match sh:
        case V.WVal{}:
          no(lg(V.JPair{kk, vv, rr}, V.WVal{}, acc), h)
        case V.WArr{}:
          no(lg(V.JPair{kk, vv, rr}, V.WArr{}, acc), h)
        case V.WObj{}:
          lexp_pair(rr, kk, vv, h, acc, xx => lexp(vv, V.WVal{}, xx,
            Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc), xx => lexp(rr, V.WObj{}, xx,
              Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TColon{} <> Lex.TStr{fixs(String.to_list(kk))} <> acc)))
    case V.JSpan{+src, +nn}:
      match sh:
        case V.WVal{}:
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)
        case V.WArr{}:
          no(lg(V.JSpan{src, nn}, V.WArr{}, acc), h)
        case V.WObj{}:
          no(lg(V.JSpan{src, nn}, V.WObj{}, acc), h)
    case V.JBind{+src, +nn, +vv, +rr}:
      match sh:
        case V.WVal{}:
          no(lg(V.JBind{src, nn, vv, rr}, V.WVal{}, acc), h)
        case V.WArr{}:
          no(lg(V.JBind{src, nn, vv, rr}, V.WArr{}, acc), h)
        case V.WObj{}:
          lexp_bind(rr, src, nn, vv, h, acc, xx => lexp(vv, V.WVal{}, xx,
            Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> acc), xx => lexp(rr, V.WObj{}, xx, Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
              tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
              U32.is_zero(nn))))} <> acc)))

# two appends of equal parts are equal
law app_cong:
  for aa: List<&2, Lex.Tok>
  for a2: List<&2, Lex.Tok>
  for bb: List<&2, Lex.Tok>
  for b2: List<&2, Lex.Tok>
  for ea: {aa == a2 : List<&2, Lex.Tok>}
  for eb: {bb == b2 : List<&2, Lex.Tok>}
  {List.append(&2, Lex.Tok, aa, bb) == List.append(&2, Lex.Tok, a2, b2) : List<&2, Lex.Tok>}

def app_cong(aa, _a2, bb, b2, ea, eb):
  %ea : {List.append(&2, Lex.Tok, aa, bb) == List.append(&2, Lex.Tok, _, b2) : List<&2, Lex.Tok>}
  %eb : {List.append(&2, Lex.Tok, aa, bb) == List.append(&2, Lex.Tok, aa, _) : List<&2, Lex.Tok>}
  {==}

# appending nothing
law lapp_nil:
  for +xs: List<&2, Lex.Tok>
  {List.append(&2, Lex.Tok, xs, []) == xs : List<&2, Lex.Tok>}

def lapp_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{hd, +tl}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => hd <> yy, List.append(&2, Lex.Tok, tl, []), tl,
        lapp_nil(tl))

# spans replaced in two token lists joined by a comma, each without spans
law dens_sep:
  for +aa: List<&2, Lex.Tok>
  for +bb: List<&2, Lex.Tok>
  for ea: {dens(aa) == aa : List<&2, Lex.Tok>}
  for eb: {dens(bb) == bb : List<&2, Lex.Tok>}
  {dens(List.append(&2, Lex.Tok, aa, Lex.TComma{} <> bb)) == List.append(&2, Lex.Tok, aa,
    Lex.TComma{} <> bb) : List<&2, Lex.Tok>}

def dens_sep(aa, bb, ea, eb):
  Equal.trans(List<&2, Lex.Tok>, dens(List.append(&2, Lex.Tok, aa, Lex.TComma{} <> bb)),
    List.append(&2, Lex.Tok, dens(aa), Lex.TComma{} <> dens(bb)), List.append(&2, Lex.Tok, aa, Lex.TComma{} <> bb),
    dens_app(aa, Lex.TComma{} <> bb),
    app_cong(dens(aa), aa, Lex.TComma{} <> dens(bb), Lex.TComma{} <> bb, ea,
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TComma{} <> yy, dens(bb), bb, eb)))

# dens_tj for a boolean
law dens_bool:
  for bb: Bool
  for sh: V.Shape
  {dens(tj(V.JBool{bb}, sh)) == tj(V.JBool{bb}, sh) : List<&2, Lex.Tok>}

def dens_bool(bb, sh):
  match bb:
    case True{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case False{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}

# dens_tj for an array cell, by what follows it
law dens_cons:
  for tl: V.Json
  for sh: V.Shape
  for +hd: V.Json
  for ih_hd: {dens(tj(hd, V.WVal{})) == tj(hd, V.WVal{}) : List<&2, Lex.Tok>}
  for ih_tl: {dens(tj(tl, V.WArr{})) == tj(tl, V.WArr{}) : List<&2, Lex.Tok>}
  {dens(tj(V.JCons{hd, tl}, sh)) == tj(V.JCons{hd, tl}, sh) : List<&2, Lex.Tok>}

def dens_cons(tl, sh, hd, ih_hd, ih_tl):
  match tl:
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          ih_hd
        case V.WObj{}:
          {==}
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(tj(hd, V.WVal{}), tj(V.JNull{}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JBool{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(tj(hd, V.WVal{}), tj(V.JBool{t1}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JNum{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(tj(hd, V.WVal{}), tj(V.JNum{t1}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JStr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(tj(hd, V.WVal{}), tj(V.JStr{t1}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JArr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(tj(hd, V.WVal{}), tj(V.JArr{t1}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JObj{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(tj(hd, V.WVal{}), tj(V.JObj{t1}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JCons{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(tj(hd, V.WVal{}), tj(V.JCons{t1, t2}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JPair{+t1, +t2, +t3}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(tj(hd, V.WVal{}), tj(V.JPair{t1, t2, t3}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JSpan{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(tj(hd, V.WVal{}), tj(V.JSpan{t1, t2}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JBind{+t1, +t2, +t3, +t4}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(tj(hd, V.WVal{}), tj(V.JBind{t1, t2, t3, t4}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}


# dens_tj for an object cell, by what follows it
law dens_pair:
  for rr: V.Json
  for sh: V.Shape
  for +kk: String
  for +vv: V.Json
  for ih_v: {dens(tj(vv, V.WVal{})) == tj(vv, V.WVal{}) : List<&2, Lex.Tok>}
  for ih_r: {dens(tj(rr, V.WObj{})) == tj(rr, V.WObj{}) : List<&2, Lex.Tok>}
  {dens(tj(V.JPair{kk, vv, rr}, sh)) == tj(V.JPair{kk, vv, rr}, sh) : List<&2, Lex.Tok>}

def dens_pair(rr, sh, kk, vv, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> yy, dens(tj(vv, V.WVal{})), tj(vv,
            V.WVal{}), ih_v)
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv,
            V.WVal{}), Lex.TComma{} <> tj(V.JNull{}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JNull{}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JNull{}, V.WObj{}), ih_v, ih_r))
    case V.JBool{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv,
            V.WVal{}), Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JBool{t1}, V.WObj{}), ih_v, ih_r))
    case V.JNum{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv,
            V.WVal{}), Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JNum{t1}, V.WObj{}), ih_v, ih_r))
    case V.JStr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv,
            V.WVal{}), Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JStr{t1}, V.WObj{}), ih_v, ih_r))
    case V.JArr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv,
            V.WVal{}), Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JArr{t1}, V.WObj{}), ih_v, ih_r))
    case V.JObj{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv,
            V.WVal{}), Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JObj{t1}, V.WObj{}), ih_v, ih_r))
    case V.JCons{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv,
            V.WVal{}), Lex.TComma{} <> tj(V.JCons{t1,
            t2}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JCons{t1, t2}, V.WObj{}), ih_v, ih_r))
    case V.JPair{+t1, +t2, +t3}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv,
            V.WVal{}), Lex.TComma{} <> tj(V.JPair{t1, t2,
            t3}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JPair{t1, t2, t3},
              V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JPair{t1, t2, t3}, V.WObj{}), ih_v, ih_r))
    case V.JSpan{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv,
            V.WVal{}), Lex.TComma{} <> tj(V.JSpan{t1,
            t2}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JSpan{t1, t2}, V.WObj{}), ih_v, ih_r))
    case V.JBind{+t1, +t2, +t3, +t4}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv,
            V.WVal{}), Lex.TComma{} <> tj(V.JBind{t1, t2, t3,
            t4}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4},
              V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JBind{t1, t2, t3, t4}, V.WObj{}), ih_v, ih_r))


# dens_tj for an object cell, by what follows it
law dens_bind:
  for rr: V.Json
  for sh: V.Shape
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for ih_v: {dens(tj(vv, V.WVal{})) == tj(vv, V.WVal{}) : List<&2, Lex.Tok>}
  for ih_r: {dens(tj(rr, V.WObj{})) == tj(rr, V.WObj{}) : List<&2, Lex.Tok>}
  {dens(tj(V.JBind{src, nn, vv, rr}, sh)) == tj(V.JBind{src, nn, vv, rr}, sh) : List<&2, Lex.Tok>}

def dens_bind(rr, sh, src, nn, vv, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> Lex.TColon{} <> yy, dens(tj(vv, V.WVal{})), tj(vv, V.WVal{}), ih_v)
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JNull{}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JNull{}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JNull{}, V.WObj{}), ih_v, ih_r))
    case V.JBool{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JBool{t1}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JBool{t1}, V.WObj{}), ih_v, ih_r))
    case V.JNum{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JNum{t1}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JNum{t1}, V.WObj{}), ih_v, ih_r))
    case V.JStr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JStr{t1}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JStr{t1}, V.WObj{}), ih_v, ih_r))
    case V.JArr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JArr{t1}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JArr{t1}, V.WObj{}), ih_v, ih_r))
    case V.JObj{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JObj{t1}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JObj{t1}, V.WObj{}), ih_v, ih_r))
    case V.JCons{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JCons{t1, t2}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JCons{t1, t2}, V.WObj{}), ih_v, ih_r))
    case V.JPair{+t1, +t2, +t3}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JPair{t1, t2, t3}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JPair{t1, t2, t3}, V.WObj{}), ih_v, ih_r))
    case V.JSpan{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JSpan{t1, t2}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JSpan{t1, t2}, V.WObj{}), ih_v, ih_r))
    case V.JBind{+t1, +t2, +t3, +t4}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> Lex.TColon{} <> yy, dens(List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WObj{}))), List.append(&2, Lex.Tok, tj(vv, V.WVal{}),
              Lex.TComma{} <> tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
            dens_sep(tj(vv, V.WVal{}), tj(V.JBind{t1, t2, t3, t4}, V.WObj{}), ih_v, ih_r))


# a value's tokens hold no spans
law dens_tj:
  for +val: V.Json
  for +sh: V.Shape
  {dens(tj(val, sh)) == tj(val, sh) : List<&2, Lex.Tok>}

def dens_tj(val, sh):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBool{bb}:
      dens_bool(bb, sh)
    case V.JNum{raw}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JStr{txt}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JArr{+items}:
      match sh:
        case V.WVal{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TOpenArr{} <> yy, dens(List.append(&2, Lex.Tok,
            tj(items, V.WArr{}), [Lex.TCloseArr{}])), List.append(&2, Lex.Tok, tj(items, V.WArr{}), [Lex.TCloseArr{}]),
            Equal.trans(List<&2, Lex.Tok>, dens(List.append(&2, Lex.Tok, tj(items, V.WArr{}), [Lex.TCloseArr{}])),
              List.append(&2, Lex.Tok, dens(tj(items, V.WArr{})), [Lex.TCloseArr{}]), List.append(&2, Lex.Tok,
              tj(items, V.WArr{}), [Lex.TCloseArr{}]),
              dens_app(tj(items, V.WArr{}), [Lex.TCloseArr{}]),
              app_cong(dens(tj(items, V.WArr{})), tj(items, V.WArr{}), [Lex.TCloseArr{}], [Lex.TCloseArr{}],
                dens_tj(items, V.WArr{}), {==})))
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JObj{+pairs}:
      match sh:
        case V.WVal{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TOpenObj{} <> yy, dens(List.append(&2, Lex.Tok,
            tj(pairs, V.WObj{}), [Lex.TCloseObj{}])), List.append(&2, Lex.Tok, tj(pairs, V.WObj{}), [Lex.TCloseObj{}]),
            Equal.trans(List<&2, Lex.Tok>, dens(List.append(&2, Lex.Tok, tj(pairs, V.WObj{}), [Lex.TCloseObj{}])),
              List.append(&2, Lex.Tok, dens(tj(pairs, V.WObj{})), [Lex.TCloseObj{}]), List.append(&2, Lex.Tok,
              tj(pairs, V.WObj{}), [Lex.TCloseObj{}]),
              dens_app(tj(pairs, V.WObj{}), [Lex.TCloseObj{}]),
              app_cong(dens(tj(pairs, V.WObj{})), tj(pairs, V.WObj{}), [Lex.TCloseObj{}], [Lex.TCloseObj{}],
                dens_tj(pairs, V.WObj{}), {==})))
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JCons{+hd, +tl}:
      dens_cons(tl, sh, hd, dens_tj(hd, V.WVal{}), dens_tj(tl, V.WArr{}))
    case V.JPair{+kk, +vv, +rr}:
      dens_pair(rr, sh, kk, vv, dens_tj(vv, V.WVal{}), dens_tj(rr, V.WObj{}))
    case V.JSpan{src, nn}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBind{+src, +nn, +vv, +rr}:
      dens_bind(rr, sh, src, nn, vv, dens_tj(vv, V.WVal{}), dens_tj(rr, V.WObj{}))

# fin_pend for a boolean
law fin_bool:
  for bb: Bool
  {Lex.finish(pend(V.JBool{bb}, [])) == tj(V.JBool{bb}, V.WVal{}) : List<&2, Lex.Tok>}

def fin_bool(bb):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# the end of a value's text closes its word, or leaves its tokens in order
law fin_pend:
  for +val: V.Json
  {Lex.finish(pend(val, [])) == tj(val, V.WVal{}) : List<&2, Lex.Tok>}

def fin_pend(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{bb}:
      fin_bool(bb)
    case V.JNum{+raw}:
      Equal.cong(String, List<&2, Lex.Tok>, xx => [Lex.TWord{xx}], Lex.text(List.reverse.go(&2, Char,
        String.to_list(raw), [])), raw,
        word_text(raw))
    case V.JStr{+a1}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, tj(V.JStr{a1},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, tj(V.JStr{a1}, V.WVal{}), []), tj(V.JStr{a1}, V.WVal{}), rev_rev(tj(V.JStr{a1},
          V.WVal{}), [], []), lapp_nil(tj(V.JStr{a1}, V.WVal{})))
    case V.JArr{+a1}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, tj(V.JArr{a1},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, tj(V.JArr{a1}, V.WVal{}), []), tj(V.JArr{a1}, V.WVal{}), rev_rev(tj(V.JArr{a1},
          V.WVal{}), [], []), lapp_nil(tj(V.JArr{a1}, V.WVal{})))
    case V.JObj{+a1}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, tj(V.JObj{a1},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, tj(V.JObj{a1}, V.WVal{}), []), tj(V.JObj{a1}, V.WVal{}), rev_rev(tj(V.JObj{a1},
          V.WVal{}), [], []), lapp_nil(tj(V.JObj{a1}, V.WVal{})))
    case V.JNil{}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, tj(V.JNil{}, V.WVal{}),
        []), []),
        List.append(&2, Lex.Tok, tj(V.JNil{}, V.WVal{}), []), tj(V.JNil{}, V.WVal{}), rev_rev(tj(V.JNil{}, V.WVal{}),
          [], []), lapp_nil(tj(V.JNil{}, V.WVal{})))
    case V.JCons{+a1, +a2}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, tj(V.JCons{a1, a2},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, tj(V.JCons{a1, a2}, V.WVal{}), []), tj(V.JCons{a1, a2},
          V.WVal{}), rev_rev(tj(V.JCons{a1, a2}, V.WVal{}), [], []), lapp_nil(tj(V.JCons{a1, a2}, V.WVal{})))
    case V.JPair{+a1, +a2, +a3}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, tj(V.JPair{a1, a2, a3},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, tj(V.JPair{a1, a2, a3}, V.WVal{}), []), tj(V.JPair{a1, a2, a3},
          V.WVal{}), rev_rev(tj(V.JPair{a1, a2, a3}, V.WVal{}), [], []), lapp_nil(tj(V.JPair{a1, a2, a3}, V.WVal{})))
    case V.JSpan{+a1, +a2}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, tj(V.JSpan{a1, a2},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, tj(V.JSpan{a1, a2}, V.WVal{}), []), tj(V.JSpan{a1, a2},
          V.WVal{}), rev_rev(tj(V.JSpan{a1, a2}, V.WVal{}), [], []), lapp_nil(tj(V.JSpan{a1, a2}, V.WVal{})))
    case V.JBind{+a1, +a2, +a3, +a4}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, tj(V.JBind{a1, a2, a3,
        a4}, V.WVal{}), []), []),
        List.append(&2, Lex.Tok, tj(V.JBind{a1, a2, a3, a4}, V.WVal{}), []), tj(V.JBind{a1, a2, a3, a4},
          V.WVal{}), rev_rev(tj(V.JBind{a1, a2, a3, a4}, V.WVal{}), [], []), lapp_nil(tj(V.JBind{a1, a2, a3, a4},
          V.WVal{})))

# WP-L2: the character lexer reads a well-formed value's text as its tokens
law lex_print:
  for +val: V.Json
  for h_wf: {V.wf(val) == True{} : Bool}
  {Lex.finish(Lex.run(String.to_list(Print.print(val)), Lex.Lex{Lex.Idle{}, [], []})) == tj(val, V.WVal{}) : List<&2,
    Lex.Tok>}

def lex_print(val, h_wf):
  Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(Print.print(val)), Lex.Lex{Lex.Idle{}, [], []})),
    Lex.finish(pend(val, [])), tj(val, V.WVal{}),
    Equal.cong(Lex.Lex, List<&2, Lex.Tok>, xx => Lex.finish(xx), Lex.run(String.to_list(Print.print(val)),
      Lex.Lex{Lex.Idle{}, [], []}),
      pend(val, []), lexp(val, V.WVal{}, h_wf, [])),
    fin_pend(val))

# WP-L2: parse's lexer reads a well-formed value's text as its tokens, up to spans
law tokens_print:
  for +val: V.Json
  for h_wf: {V.wf(val) == True{} : Bool}
  for h_s: {Laws.short(Print.print(val)) == True{} : Bool}
  {dens(Lex.tokens(Print.print(val))) == tj(val, V.WVal{}) : List<&2, Lex.Tok>}

def tokens_print(val, h_wf, h_s):
  +txt = Print.print(val)
  +lx = Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))
  Equal.trans(List<&2, Lex.Tok>, dens(Lex.tokens(txt)), dens(lx), tj(val, V.WVal{}), lexers_agree(txt, h_s),
    Equal.trans(List<&2, Lex.Tok>, dens(lx), dens(tj(val, V.WVal{})), tj(val, V.WVal{}),
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, xx => dens(xx), lx, tj(val, V.WVal{}), lex_print(val, h_wf)),
      dens_tj(val, V.WVal{})))

# what esc_ctl says of a control, its other hypotheses first
def esc_eq(uu: U32) -> Type:
  {Print.escape.char(Chr{uu}) == "\\u00" ++ String.from_list([Laws.char_at(Laws.hex_lower(), U32.to_nat(U32.div(uu,
    16))),
    Laws.char_at(Laws.hex_lower(), U32.to_nat(U32.mod(uu, 16)))]) : String}

def esc_goal(uu: U32) -> Type:
  {Chr{uu} != '\u{8}' : Char} -> {Chr{uu} != '\u{c}' : Char} -> {Chr{uu} != '\n' : Char} ->
    {Chr{uu} != '\r' : Char} -> {Chr{uu} != '\t' : Char} -> esc_eq(uu)

# esc_ctl, one control at a time
law esc_ctl5:
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, zw(26n)}}}}}}})

def esc_ctl5(b0, b1, b2, b3, b4):
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} False{} False{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} False{} False{} True{} False{}:
      h_b => _h_f => _h_n => _h_r => _h_t => Empty.absurd(esc_eq(U32{WCon{False{}, WCon{False{}, WCon{False{},
        WCon{True{}, WCon{False{}, WCon{False{}, zw(26n)}}}}}}}), h_b({==}))
    case False{} False{} False{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} False{} True{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} False{} True{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} False{} True{} True{} False{}:
      _h_b => h_f => _h_n => _h_r => _h_t => Empty.absurd(esc_eq(U32{WCon{False{}, WCon{False{}, WCon{True{},
        WCon{True{}, WCon{False{}, WCon{False{}, zw(26n)}}}}}}}), h_f({==}))
    case False{} False{} True{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} False{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} False{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} False{} True{} False{}:
      _h_b => _h_f => h_n => _h_r => _h_t => Empty.absurd(esc_eq(U32{WCon{False{}, WCon{True{}, WCon{False{},
        WCon{True{}, WCon{False{}, WCon{False{}, zw(26n)}}}}}}}), h_n({==}))
    case False{} True{} False{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} True{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} True{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} True{} True{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} True{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} False{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} False{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} False{} True{} False{}:
      _h_b => _h_f => _h_n => _h_r => h_t => Empty.absurd(esc_eq(U32{WCon{True{}, WCon{False{}, WCon{False{},
        WCon{True{}, WCon{False{}, WCon{False{}, zw(26n)}}}}}}}), h_t({==}))
    case True{} False{} False{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} True{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} True{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} True{} True{} False{}:
      _h_b => _h_f => _h_n => h_r => _h_t => Empty.absurd(esc_eq(U32{WCon{True{}, WCon{False{}, WCon{True{},
        WCon{True{}, WCon{False{}, WCon{False{}, zw(26n)}}}}}}}), h_r({==}))
    case True{} False{} True{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} False{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} False{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} False{} True{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} False{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} True{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} True{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} True{} True{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} True{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}

# esc_ctl, once bit 5 and the bits above are known
law esc_ctl.at:
  for cc: Cmp
  for b5: Bool
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for +rest: Word(26n)
  for ec: {Word.cmp(26n, rest, zw(26n)) == cc : Cmp}
  for h_lt: {Cmp.is_lt(Word.cmp.fin(b5, True{}, cc)) == True{} : Bool}
  esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}})

def esc_ctl.at(cc, b5, b0, b1, b2, b3, b4, rest, ec, h_lt):
  match cc:
    case LT{}:
      ez = Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, rest, zw(26n)), LT{}, ec)
      Empty.absurd(esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
        true_false(Equal.trans(Bool, True{},
        Cmp.is_lt(Word.cmp(26n, rest, zw(26n))), False{},
        Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, rest, zw(26n))), True{}, ez), zw_nlt(26n, rest))))
    case GT{}:
      match b5:
        case False{}:
          Empty.absurd(esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, rest}}}}}}}),
            false_true(h_lt))
        case True{}:
          Empty.absurd(esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{}, rest}}}}}}}),
            false_true(h_lt))
    case EQ{}:
      match b5:
        case True{}:
          Empty.absurd(esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{}, rest}}}}}}}),
            false_true(h_lt))
        case False{}:
          er = Equal.sym(Word(26n), rest, zw(26n),
            weq(26n, rest, zw(26n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(26n, rest, zw(26n)), EQ{}, ec)))
          %er : esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, _}}}}}}})
          esc_ctl5(b0, b1, b2, b3, b4)

# a control below U+0020, other than the five with two-character escapes
law esc_ctl.go:
  for +uu: U32
  for h_lt: {U32.is_lt(uu, 32) == True{} : Bool}
  esc_goal(uu)

def esc_ctl.go(uu, h_lt):
  match uu:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +rest}}}}}}}:
      +c5 = Word.cmp.fin(b5, True{}, Word.cmp(26n, rest, zw(26n)))
      +c4 = Word.cmp.fin(b4, False{}, c5)
      +c3 = Word.cmp.fin(b3, False{}, c4)
      +c2 = Word.cmp.fin(b2, False{}, c3)
      +c1 = Word.cmp.fin(b1, False{}, c2)
      h5 = lt_up(b4, c5, lt_up(b3, c4, lt_up(b2, c3, lt_up(b1, c2, lt_up(b0, c1, h_lt)))))
      esc_ctl.at(Word.cmp(26n, rest, zw(26n)), b5, b0, b1, b2, b3, b4, rest, {==}, h5)

def Laws.esc_ctl(ch, h_ctl, h_b, h_f, h_n, h_r, h_t):
  match ch:
    case Chr{+uu}:
      esc_ctl.go(uu, h_ctl)(h_b, h_f, h_n, h_r, h_t)

# JSON-STR-1: a printed string parses back

# a scalar value is its own fix
law fix_id:
  for +ch: Char
  for h_sc: {Bool.not(Laws.non_scalar(Char.to_u32(ch))) == True{} : Bool}
  {fix(ch) == ch : Char}

def fix_id(ch, h_sc):
  match ch:
    case Chr{+uu}:
      hs = Equal.sym(Bool, Bool.not(Laws.non_scalar(uu)), True{}, h_sc)
      %hs : {Bool.pick(Char, _, Chr{uu}, Chr{65533}) == Chr{uu} : Char}
      {==}

# a text of scalar values is its own fix
law fixs_id:
  for +txt: String
  for +h_sc: {Laws.scalars(txt) == True{} : Bool}
  {fixs(String.to_list(txt)) == txt : String}

def fixs_id(txt, h_sc):
  match txt:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      +ok = Bool.not(Laws.non_scalar(Char.to_u32(hd)))
      eh = fix_id(hd, and_left(ok, Laws.scalars(tl), h_sc))
      et = fixs_id(tl, and_right(ok, Laws.scalars(tl), h_sc))
      Equal.trans(String, SCon{fix(hd), fixs(String.to_list(tl))}, SCon{hd, fixs(String.to_list(tl))}, SCon{hd, tl},
        Equal.cong(Char, String, xx => SCon{xx, fixs(String.to_list(tl))}, fix(hd), hd, eh),
        Equal.cong(String, String, xx => SCon{hd, xx}, fixs(String.to_list(tl)), tl, et))

# whether a token is a string token
def is_tstr(tok: Lex.Tok) -> Bool:
  match tok:
    case Lex.TStr{_}:
      True{}
    case _:
      False{}

# a string token's text
def tstr_of(tok: Lex.Tok) -> String:
  match tok:
    case Lex.TStr{txt}:
      txt
    case _:
      ""

# whether a list is empty
def tnil(xs: List<&2, Lex.Tok>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case _:
      False{}

# the first token of a list, or a bad one
def thead(xs: List<&2, Lex.Tok>) -> Lex.Tok:
  match xs:
    case Nil{}:
      Lex.TBad{}
    case hd <> _:
      hd

# the tokens after the first
def ttail(xs: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match xs:
    case Nil{}:
      Nil{}
    case _ <> tl:
      tl

# a token that means a string parses, alone, as a string of its characters
law one_tok:
  for tok: Lex.Tok
  for +txt: String
  for eh: {den(tok) == Lex.TStr{txt} : Lex.Tok}
  {Laws.str_of(Parse.finish(Parse.run([tok], Parse.P{False{}, None{}, Nil{}}))) == Some{txt} : Maybe<&2, String>}

def one_tok(tok, txt, eh):
  match tok:
    case Lex.TStr{+yy}:
      Equal.cong(String, Maybe<&2, String>, xx => Some{xx}, yy, txt,
        Equal.cong(Lex.Tok, String, xx => tstr_of(xx), Lex.TStr{yy}, Lex.TStr{txt}, eh))
    case Lex.TStrS{+src, +nn}:
      Equal.cong(String, Maybe<&2, String>, xx => Some{xx}, V.span.str(src, nn, U32.is_zero(nn)), txt,
        Equal.cong(Lex.Tok, String, xx => tstr_of(xx), Lex.TStr{V.span.str(src, nn, U32.is_zero(nn))}, Lex.TStr{txt},
          eh))
    case Lex.TOpenArr{}:
      Empty.absurd({Laws.str_of(Parse.finish(Parse.run([Lex.TOpenArr{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TOpenArr{},
          Lex.TStr{txt}, eh)))
    case Lex.TCloseArr{}:
      Empty.absurd({Laws.str_of(Parse.finish(Parse.run([Lex.TCloseArr{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TCloseArr{},
          Lex.TStr{txt}, eh)))
    case Lex.TOpenObj{}:
      Empty.absurd({Laws.str_of(Parse.finish(Parse.run([Lex.TOpenObj{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TOpenObj{},
          Lex.TStr{txt}, eh)))
    case Lex.TCloseObj{}:
      Empty.absurd({Laws.str_of(Parse.finish(Parse.run([Lex.TCloseObj{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TCloseObj{},
          Lex.TStr{txt}, eh)))
    case Lex.TColon{}:
      Empty.absurd({Laws.str_of(Parse.finish(Parse.run([Lex.TColon{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TColon{},
          Lex.TStr{txt}, eh)))
    case Lex.TComma{}:
      Empty.absurd({Laws.str_of(Parse.finish(Parse.run([Lex.TComma{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TComma{},
          Lex.TStr{txt}, eh)))
    case Lex.TWord{+raw}:
      Empty.absurd({Laws.str_of(Parse.finish(Parse.run([Lex.TWord{raw}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TWord{raw},
          Lex.TStr{txt}, eh)))
    case Lex.TWordS{+src, +nn}:
      Empty.absurd({Laws.str_of(Parse.finish(Parse.run([Lex.TWordS{src, nn}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx),
          Lex.TWord{V.span.str(src, nn, U32.is_zero(nn))}, Lex.TStr{txt}, eh)))
    case Lex.TBad{}:
      Empty.absurd({Laws.str_of(Parse.finish(Parse.run([Lex.TBad{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TBad{},
          Lex.TStr{txt}, eh)))

# one_str, once the list is split
law one_str.at:
  for rest: List<&2, Lex.Tok>
  for tok: Lex.Tok
  for +txt: String
  for eh: {den(tok) == Lex.TStr{txt} : Lex.Tok}
  for er: {dens(rest) == [] : List<&2, Lex.Tok>}
  {Laws.str_of(Parse.finish(Parse.run(tok <> rest, Parse.P{False{}, None{}, Nil{}}))) == Some{txt} :
    Maybe<&2, String>}

def one_str.at(rest, tok, txt, eh, er):
  match rest:
    case Nil{}:
      one_tok(tok, txt, eh)
    case r1 <> r2:
      Empty.absurd({Laws.str_of(Parse.finish(Parse.run(tok <> r1 <> r2, Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, false_true(Equal.cong(List<&2, Lex.Tok>, Bool, xx => tnil(xx),
          den(r1) <> dens(r2), [], er)))

# tokens that mean one string token parse as a string of its characters
law one_str:
  for xs: List<&2, Lex.Tok>
  for +txt: String
  for +ex: {dens(xs) == [Lex.TStr{txt}] : List<&2, Lex.Tok>}
  {Laws.str_of(Parse.finish(Parse.run(xs, Parse.P{False{}, None{}, Nil{}}))) == Some{txt} : Maybe<&2, String>}

def one_str(xs, txt, ex):
  match xs:
    case Nil{}:
      Empty.absurd({Laws.str_of(Parse.finish(Parse.run([], Parse.P{False{}, None{}, Nil{}}))) == Some{txt} :
        Maybe<&2, String>}, true_false(Equal.cong(List<&2, Lex.Tok>, Bool, yy => tnil(yy), [], [Lex.TStr{txt}], ex)))
    case +hd <> +tl:
      one_str.at(tl, hd, txt,
        Equal.cong(List<&2, Lex.Tok>, Lex.Tok, yy => thead(yy), den(hd) <> dens(tl), [Lex.TStr{txt}], ex),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => ttail(yy), den(hd) <> dens(tl), [Lex.TStr{txt}], ex))

def Laws.str_back(txt, h_sc, h_s):
  +got = fixs(String.to_list(txt))
  Equal.trans(Maybe<&2, String>, Laws.str_of(Parse.parse(Print.quote(txt))), Some{got}, Some{txt},
    one_str(Lex.tokens(Print.quote(txt)), got, tokens_print(V.JStr{txt}, {==}, h_s)),
    Equal.cong(String, Maybe<&2, String>, xx => Some{xx}, got, txt, fixs_id(txt, h_sc)))

# WP-P1: the parser on a value's tokens

# comparing two strings, one character in front of each, answers as the rest
law cmp_rec_eq:
  for h1: Char
  for h2: Char
  for rr: (String & String) & Cmp
  {String.eq.fin(String.cmp.rec(h1, h2, rr)) == String.eq.fin(rr) : Bool}

def cmp_rec_eq(_h1, _h2, rr):
  ((_a, _b), _c) = rr
  {==}

# str_eq_sound, once the first characters' comparison is named
law str_eq_at:
  for cc: Cmp
  for +xx: U32
  for +yy: U32
  for +t1: String
  for +t2: String
  for ec: {U32.cmp(xx, yy) == cc : Cmp}
  for h: {String.eq.fin(String.cmp.fin(t1, t2, ((Chr{xx}, Chr{yy}), cc))) == True{} : Bool}
  for ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String}
  {SCon{Chr{xx}, t1} == SCon{Chr{yy}, t2} : String}

def str_eq_at(cc, xx, yy, t1, t2, ec, h, ih):
  match cc:
    case LT{}:
      Empty.absurd({SCon{Chr{xx}, t1} == SCon{Chr{yy}, t2} : String}, false_true(h))
    case GT{}:
      Empty.absurd({SCon{Chr{xx}, t1} == SCon{Chr{yy}, t2} : String}, false_true(h))
    case EQ{}:
      et = ih(Equal.trans(Bool, String.eq(t1, t2), String.eq.fin(String.cmp.rec(Chr{xx}, Chr{yy}, String.cmp(t1, t2))),
        True{}, Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{xx}, Chr{yy}, String.cmp(t1, t2))), String.eq(t1, t2),
          cmp_rec_eq(Chr{xx}, Chr{yy}, String.cmp(t1, t2))), h))
      ex = ueq(xx, yy, Equal.cong(Cmp, Bool, zz => Cmp.is_eq(zz), U32.cmp(xx, yy), EQ{}, ec))
      %ex : {SCon{Chr{xx}, t1} == SCon{Chr{_}, t2} : String}
      %et : {SCon{Chr{xx}, t1} == SCon{Chr{xx}, _} : String}
      {==}

# strings String.eq calls equal are equal
law str_eq_sound:
  for +aa: String
  for +bb: String
  for h: {String.eq(aa, bb) == True{} : Bool}
  {aa == bb : String}

def str_eq_sound(aa, bb, h):
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h2, t2}:
      Empty.absurd({SNil{} == SCon{h2, t2} : String}, false_true(h))
    case SCon{h1, t1} SNil{}:
      Empty.absurd({SCon{h1, t1} == SNil{} : String}, false_true(h))
    case SCon{Chr{+xx}, +t1} SCon{Chr{+yy}, +t2}:
      str_eq_at(U32.cmp(xx, yy), xx, yy, t1, t2, {==}, h, hh => str_eq_sound(t1, t2, hh))

# a word equal to a literal is no number
law lit_not_num:
  for +raw: String
  for +lit: String
  for e_lit: {String.eq(raw, lit) == True{} : Bool}
  for h_lit: {V.num.ok(lit) == False{} : Bool}
  for h_num: {V.num.ok(raw) == True{} : Bool}
  Empty

def lit_not_num(raw, lit, e_lit, h_lit, h_num):
  true_false(Equal.trans(Bool, True{}, V.num.ok(raw), False{}, Equal.sym(Bool, V.num.ok(raw), True{}, h_num),
    Equal.trans(Bool, V.num.ok(raw), V.num.ok(lit), False{},
      Equal.cong(String, Bool, zz => V.num.ok(zz), raw, lit, str_eq_sound(raw, lit, e_lit)), h_lit)))

# a number's word, with the literal tests named: the parser takes it as that number
law word_num.at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +raw: String
  for e1: {String.eq(raw, "null") == b1 : Bool}
  for e2: {String.eq(raw, "true") == b2 : Bool}
  for e3: {String.eq(raw, "false") == b3 : Bool}
  for +h_num: {V.num.ok(raw) == True{} : Bool}
  ({Bool.pick(V.Json, b1, V.JNull{}, Bool.pick(V.Json, b2, V.JBool{True{}}, Bool.pick(V.Json, b3, V.JBool{False{}},
    V.JNum{raw}))) == V.JNum{raw} : V.Json} & {Bool.or(b1, Bool.or(b2, Bool.or(b3, V.num.ok(raw)))) == True{} : Bool})

def word_num.at(b1, b2, b3, raw, e1, e2, e3, h_num):
  match b1:
    case True{}:
      Empty.absurd(({V.JNull{} == V.JNum{raw} : V.Json} & {True{} == True{} : Bool}),
        lit_not_num(raw, "null", e1, {==}, h_num))
    case False{}:
      match b2:
        case True{}:
          Empty.absurd(({V.JBool{True{}} == V.JNum{raw} : V.Json} & {True{} == True{} : Bool}),
            lit_not_num(raw, "true", e2, {==}, h_num))
        case False{}:
          match b3:
            case True{}:
              Empty.absurd(({V.JBool{False{}} == V.JNum{raw} : V.Json} & {True{} == True{} : Bool}),
                lit_not_num(raw, "false", e3, {==}, h_num))
            case False{}:
              ({==}, h_num)

# step_num, with the word's two facts in hand
law step_num.go:
  for +raw: String
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for both: ({Parse.word(raw) == V.JNum{raw} : V.Json} & {Parse.word.ok(raw) == True{} : Bool})
  {Parse.step.word(raw, Parse.P{bad, root, stk}) == Parse.put(stk, root, V.JNum{raw}, bad) : Parse.P}

def step_num.go(raw, bad, root, stk, both):
  (ew, eo) = both
  ok = Equal.sym(Bool, Parse.word.ok(raw), True{}, eo)
  %ok : {Parse.step.word.go(raw, Parse.P{bad, root, stk}, _) == Parse.put(stk, root, V.JNum{raw}, bad) : Parse.P}
  ws = Equal.sym(V.Json, Parse.word(raw), V.JNum{raw}, ew)
  %ws : {Parse.put(stk, root, _, bad) == Parse.put(stk, root, V.JNum{raw}, bad) : Parse.P}
  {==}

# the parser on a number's word, at a place a value may go
law step_num:
  for +raw: String
  for h_num: {V.num.ok(raw) == True{} : Bool}
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {Parse.step.word(raw, Parse.P{bad, root, stk}) == Parse.put(stk, root, V.JNum{raw}, bad) : Parse.P}

def step_num(raw, h_num, bad, root, stk):
  both = word_num.at(String.eq(raw, "null"), String.eq(raw, "true"), String.eq(raw, "false"), raw, {==}, {==}, {==},
    h_num)
  step_num.go(raw, bad, root, stk, both)

# a value as parse builds it back from its tokens: strings owned and fixed,
# span keys owned, by shape as tj reads it
def canon(val: V.Json, sh: V.Shape) -> V.Json:
  match val sh:
    case V.JNull{} V.WVal{}:
      V.JNull{}
    case V.JBool{bb} V.WVal{}:
      V.JBool{bb}
    case V.JNum{raw} V.WVal{}:
      V.JNum{raw}
    case V.JStr{txt} V.WVal{}:
      V.JStr{fixs(String.to_list(txt))}
    case V.JSpan{src, +nn} V.WVal{}:
      V.JStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))}
    case V.JArr{items} V.WVal{}:
      V.JArr{canon(items, V.WArr{})}
    case V.JObj{pairs} V.WVal{}:
      V.JObj{canon(pairs, V.WObj{})}
    case V.JCons{hd, tl} V.WArr{}:
      V.JCons{canon(hd, V.WVal{}), canon(tl, V.WArr{})}
    case V.JPair{kk, vv, rr} V.WObj{}:
      V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), canon(rr, V.WObj{})}
    case V.JBind{src, +nn, vv, rr} V.WObj{}:
      V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), canon(rr, V.WObj{})}
    case _ _:
      V.JNil{}

# an array's cells pushed, as parse pushes them, onto its frame's items
def rpush(cells: V.Json, acc: V.Json) -> V.Json:
  match cells:
    case V.JCons{hd, tl}:
      rpush(tl, V.JCons{canon(hd, V.WVal{}), acc})
    case _:
      acc

# an object's cells pushed, as parse pushes them, onto its frame's pairs
def ppush(cells: V.Json, acc: V.Json) -> V.Json:
  match cells:
    case V.JPair{kk, vv, rr}:
      ppush(rr, V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc})
    case V.JBind{src, +nn, vv, rr}:
      ppush(rr, V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc})
    case _:
      acc

# an array frame's slot after its cells: a value still, when there were none
def aslot(cells: V.Json) -> Parse.Slot:
  match cells:
    case V.JNil{}:
      Parse.SValue{}
    case _:
      Parse.SComma{}

# an object frame's slot after its cells: a key still, when there were none
def oslot(cells: V.Json) -> Parse.Slot:
  match cells:
    case V.JNil{}:
      Parse.SKey{}
    case _:
      Parse.SComma{}

# the parser on two token lists is the parser on the first, then the second
law prun_app:
  for +xs: List<&2, Lex.Tok>
  for +ys: List<&2, Lex.Tok>
  for +st: Parse.P
  {Parse.run(List.append(&2, Lex.Tok, xs, ys), st) == Parse.run(ys, Parse.run(xs, st)) : Parse.P}

def prun_app(xs, ys, st):
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      prun_app(tl, ys, Parse.step(hd, st))

# what put_str_ready says
def psr_goal(+stk: List<&2, Parse.Frame>, +root: Maybe<&2, V.Json>, +txt: String, +bad: Bool) -> Type:
  {Parse.put.str(stk, root, Parse.KOwn{txt}, bad) == Parse.put(stk, root, V.JStr{txt}, bad) : Parse.P}

# a string where a value may go is that value
law put_str_ready:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +txt: String
  for +bad: Bool
  for h: {Parse.step.ready(stk, root) == True{} : Bool}
  psr_goal(stk, root, txt, bad)

def put_str_ready(stk, root, txt, bad, h):
  match stk:
    case Nil{}:
      match root:
        case None{}:
          {==}
        case Some{+rr}:
          Empty.absurd(psr_goal([], Some{rr}, txt, bad), false_true(h))
    case +fr <> +rest:
      match fr:
        case Parse.FArr{+items, +slot}:
          match slot:
            case Parse.SValue{}:
              {==}
            case Parse.SComma{}:
              Empty.absurd(psr_goal(Parse.FArr{items, Parse.SComma{}} <> rest, root, txt, bad), false_true(h))
            case Parse.SKey{}:
              Empty.absurd(psr_goal(Parse.FArr{items, Parse.SKey{}} <> rest, root, txt, bad), false_true(h))
            case Parse.SColon{}:
              Empty.absurd(psr_goal(Parse.FArr{items, Parse.SColon{}} <> rest, root, txt, bad), false_true(h))
        case Parse.FObj{+pairs, +key, +slot}:
          match slot:
            case Parse.SValue{}:
              {==}
            case Parse.SComma{}:
              Empty.absurd(psr_goal(Parse.FObj{pairs, key, Parse.SComma{}} <> rest, root, txt, bad), false_true(h))
            case Parse.SKey{}:
              Empty.absurd(psr_goal(Parse.FObj{pairs, key, Parse.SKey{}} <> rest, root, txt, bad), false_true(h))
            case Parse.SColon{}:
              Empty.absurd(psr_goal(Parse.FObj{pairs, key, Parse.SColon{}} <> rest, root, txt, bad), false_true(h))

# `[` where a value may go opens an array
law open_arr_ready:
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for h: {Parse.step.ready(stk, root) == True{} : Bool}
  {Parse.step.open_arr(Parse.P{bad, root, stk}) == Parse.P{bad, root, Parse.FArr{V.JNil{},
    Parse.SValue{}} <> stk} : Parse.P}

def open_arr_ready(bad, root, stk, h):
  hs = Equal.sym(Bool, Parse.step.ready(stk, root), True{}, h)
  %hs : {Parse.step.open_arr.go(bad, root, stk, _) == Parse.P{bad, root, Parse.FArr{V.JNil{},
    Parse.SValue{}} <> stk} : Parse.P}
  {==}

# `{` where a value may go opens an object
law open_obj_ready:
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for h: {Parse.step.ready(stk, root) == True{} : Bool}
  {Parse.step.open_obj(Parse.P{bad, root, stk}) == Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""},
    Parse.SKey{}} <> stk} : Parse.P}

def open_obj_ready(bad, root, stk, h):
  hs = Equal.sym(Bool, Parse.step.ready(stk, root), True{}, h)
  %hs : {Parse.step.open_obj.go(bad, root, stk, _) == Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""},
    Parse.SKey{}} <> stk} : Parse.P}
  {==}

# `]` after an array's cells and a value
law close_arr_comma:
  for +items: V.Json
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  {Parse.close_arr(Parse.FArr{items, Parse.SComma{}} <> stk, root, bad) ==
    Parse.put(stk, root, V.JArr{V.reverse(items, V.JNil{})}, bad) : Parse.P}

def close_arr_comma(items, _stk, _root, _bad):
  match items:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

# `}` after an object's cells and a value
law close_obj_comma:
  for +pairs: V.Json
  for +key: Parse.Key
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  {Parse.close_obj(Parse.FObj{pairs, key, Parse.SComma{}} <> stk, root, bad) ==
    Parse.put(stk, root, V.JObj{V.reverse(pairs, V.JNil{})}, bad) : Parse.P}

def close_obj_comma(pairs, _key, _stk, _root, _bad):
  match pairs:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

# pushing an array's cells then reversing them gives the cells back in order
law rev_rpush:
  for +cells: V.Json
  for +acc: V.Json
  {V.reverse(rpush(cells, acc), V.JNil{}) == V.reverse(acc, canon(cells, V.WArr{})) : V.Json}

def rev_rpush(cells, acc):
  match cells:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      rev_rpush(x2, V.JCons{canon(x1, V.WVal{}), acc})
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

# pushing an object's cells then reversing them gives the cells back in order
law rev_ppush:
  for +cells: V.Json
  for +acc: V.Json
  {V.reverse(ppush(cells, acc), V.JNil{}) == V.reverse(acc, canon(cells, V.WObj{})) : V.Json}

def rev_ppush(cells, acc):
  match cells:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      rev_ppush(x3, V.JPair{fixs(String.to_list(x1)), canon(x2, V.WVal{}), acc})
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      rev_ppush(x4, V.JPair{fixs(String.to_list(V.span.str(x1, x2, U32.is_zero(x2)))), canon(x3, V.WVal{}), acc})

# `]` after an array's cells
law close_after_arr:
  for +items: V.Json
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {Parse.close_arr(Parse.FArr{rpush(items, V.JNil{}), aslot(items)} <> stk, root, bad) ==
    Parse.put(stk, root, V.JArr{canon(items, V.WArr{})}, bad) : Parse.P}

def close_after_arr(items, bad, root, stk):
  match items:

    case V.JNull{}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush(V.JNull{}, V.JNil{}), Parse.SComma{}} <> stk, root, bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush(V.JNull{}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon(V.JNull{}, V.WArr{})}, bad), close_arr_comma(rpush(V.JNull{}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush(V.JNull{}, V.JNil{}),
          V.JNil{}), canon(V.JNull{}, V.WArr{}), rev_rpush(V.JNull{}, V.JNil{})))
    case V.JBool{+x1}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush(V.JBool{x1}, V.JNil{}), Parse.SComma{}} <> stk, root, bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush(V.JBool{x1}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon(V.JBool{x1}, V.WArr{})}, bad), close_arr_comma(rpush(V.JBool{x1}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush(V.JBool{x1},
          V.JNil{}), V.JNil{}), canon(V.JBool{x1}, V.WArr{}), rev_rpush(V.JBool{x1}, V.JNil{})))
    case V.JNum{+x1}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush(V.JNum{x1}, V.JNil{}), Parse.SComma{}} <> stk, root, bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush(V.JNum{x1}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon(V.JNum{x1}, V.WArr{})}, bad), close_arr_comma(rpush(V.JNum{x1}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush(V.JNum{x1}, V.JNil{}),
          V.JNil{}), canon(V.JNum{x1}, V.WArr{}), rev_rpush(V.JNum{x1}, V.JNil{})))
    case V.JStr{+x1}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush(V.JStr{x1}, V.JNil{}), Parse.SComma{}} <> stk, root, bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush(V.JStr{x1}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon(V.JStr{x1}, V.WArr{})}, bad), close_arr_comma(rpush(V.JStr{x1}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush(V.JStr{x1}, V.JNil{}),
          V.JNil{}), canon(V.JStr{x1}, V.WArr{}), rev_rpush(V.JStr{x1}, V.JNil{})))
    case V.JArr{+x1}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush(V.JArr{x1}, V.JNil{}), Parse.SComma{}} <> stk, root, bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush(V.JArr{x1}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon(V.JArr{x1}, V.WArr{})}, bad), close_arr_comma(rpush(V.JArr{x1}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush(V.JArr{x1}, V.JNil{}),
          V.JNil{}), canon(V.JArr{x1}, V.WArr{}), rev_rpush(V.JArr{x1}, V.JNil{})))
    case V.JObj{+x1}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush(V.JObj{x1}, V.JNil{}), Parse.SComma{}} <> stk, root, bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush(V.JObj{x1}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon(V.JObj{x1}, V.WArr{})}, bad), close_arr_comma(rpush(V.JObj{x1}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush(V.JObj{x1}, V.JNil{}),
          V.JNil{}), canon(V.JObj{x1}, V.WArr{}), rev_rpush(V.JObj{x1}, V.JNil{})))
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush(V.JCons{x1, x2}, V.JNil{}), Parse.SComma{}} <> stk, root,
        bad), Parse.put(stk, root, V.JArr{V.reverse(rpush(V.JCons{x1, x2}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk,
        root, V.JArr{canon(V.JCons{x1, x2}, V.WArr{})}, bad), close_arr_comma(rpush(V.JCons{x1, x2}, V.JNil{}), stk,
        root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush(V.JCons{x1, x2},
          V.JNil{}), V.JNil{}), canon(V.JCons{x1, x2}, V.WArr{}), rev_rpush(V.JCons{x1, x2}, V.JNil{})))
    case V.JPair{+x1, +x2, +x3}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush(V.JPair{x1, x2, x3}, V.JNil{}), Parse.SComma{}} <> stk,
        root, bad), Parse.put(stk, root, V.JArr{V.reverse(rpush(V.JPair{x1, x2, x3}, V.JNil{}), V.JNil{})}, bad),
        Parse.put(stk, root, V.JArr{canon(V.JPair{x1, x2, x3}, V.WArr{})}, bad), close_arr_comma(rpush(V.JPair{x1, x2,
        x3}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush(V.JPair{x1, x2, x3},
          V.JNil{}), V.JNil{}), canon(V.JPair{x1, x2, x3}, V.WArr{}), rev_rpush(V.JPair{x1, x2, x3}, V.JNil{})))
    case V.JSpan{+x1, +x2}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush(V.JSpan{x1, x2}, V.JNil{}), Parse.SComma{}} <> stk, root,
        bad), Parse.put(stk, root, V.JArr{V.reverse(rpush(V.JSpan{x1, x2}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk,
        root, V.JArr{canon(V.JSpan{x1, x2}, V.WArr{})}, bad), close_arr_comma(rpush(V.JSpan{x1, x2}, V.JNil{}), stk,
        root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush(V.JSpan{x1, x2},
          V.JNil{}), V.JNil{}), canon(V.JSpan{x1, x2}, V.WArr{}), rev_rpush(V.JSpan{x1, x2}, V.JNil{})))
    case V.JBind{+x1, +x2, +x3, +x4}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush(V.JBind{x1, x2, x3, x4}, V.JNil{}), Parse.SComma{}} <> stk,
        root, bad), Parse.put(stk, root, V.JArr{V.reverse(rpush(V.JBind{x1, x2, x3, x4}, V.JNil{}), V.JNil{})}, bad),
        Parse.put(stk, root, V.JArr{canon(V.JBind{x1, x2, x3, x4}, V.WArr{})}, bad), close_arr_comma(rpush(V.JBind{x1,
        x2, x3, x4}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush(V.JBind{x1, x2, x3,
          x4}, V.JNil{}), V.JNil{}), canon(V.JBind{x1, x2, x3, x4}, V.WArr{}), rev_rpush(V.JBind{x1, x2, x3, x4},
          V.JNil{})))

# `}` after an object's cells
law close_after_obj:
  for +pairs: V.Json
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {Parse.close_obj(Parse.FObj{ppush(pairs, V.JNil{}), Parse.KOwn{""}, oslot(pairs)} <> stk, root, bad) ==
    Parse.put(stk, root, V.JObj{canon(pairs, V.WObj{})}, bad) : Parse.P}

def close_after_obj(pairs, bad, root, stk):
  match pairs:
    case V.JNull{}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush(V.JNull{}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush(V.JNull{}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon(V.JNull{}, V.WObj{})}, bad),
        close_obj_comma(ppush(V.JNull{}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush(V.JNull{}, V.JNil{}),
          V.JNil{}), canon(V.JNull{}, V.WObj{}), rev_ppush(V.JNull{}, V.JNil{})))
    case V.JBool{+x1}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush(V.JBool{x1}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush(V.JBool{x1}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon(V.JBool{x1}, V.WObj{})}, bad),
        close_obj_comma(ppush(V.JBool{x1}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush(V.JBool{x1},
          V.JNil{}), V.JNil{}), canon(V.JBool{x1}, V.WObj{}), rev_ppush(V.JBool{x1}, V.JNil{})))
    case V.JNum{+x1}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush(V.JNum{x1}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush(V.JNum{x1}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon(V.JNum{x1}, V.WObj{})}, bad),
        close_obj_comma(ppush(V.JNum{x1}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush(V.JNum{x1}, V.JNil{}),
          V.JNil{}), canon(V.JNum{x1}, V.WObj{}), rev_ppush(V.JNum{x1}, V.JNil{})))
    case V.JStr{+x1}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush(V.JStr{x1}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush(V.JStr{x1}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon(V.JStr{x1}, V.WObj{})}, bad),
        close_obj_comma(ppush(V.JStr{x1}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush(V.JStr{x1}, V.JNil{}),
          V.JNil{}), canon(V.JStr{x1}, V.WObj{}), rev_ppush(V.JStr{x1}, V.JNil{})))
    case V.JArr{+x1}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush(V.JArr{x1}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush(V.JArr{x1}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon(V.JArr{x1}, V.WObj{})}, bad),
        close_obj_comma(ppush(V.JArr{x1}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush(V.JArr{x1}, V.JNil{}),
          V.JNil{}), canon(V.JArr{x1}, V.WObj{}), rev_ppush(V.JArr{x1}, V.JNil{})))
    case V.JObj{+x1}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush(V.JObj{x1}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush(V.JObj{x1}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon(V.JObj{x1}, V.WObj{})}, bad),
        close_obj_comma(ppush(V.JObj{x1}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush(V.JObj{x1}, V.JNil{}),
          V.JNil{}), canon(V.JObj{x1}, V.WObj{}), rev_ppush(V.JObj{x1}, V.JNil{})))
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush(V.JCons{x1, x2}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush(V.JCons{x1, x2}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon(V.JCons{x1, x2}, V.WObj{})}, bad),
        close_obj_comma(ppush(V.JCons{x1, x2}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush(V.JCons{x1, x2},
          V.JNil{}), V.JNil{}), canon(V.JCons{x1, x2}, V.WObj{}), rev_ppush(V.JCons{x1, x2}, V.JNil{})))
    case V.JPair{+x1, +x2, +x3}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush(V.JPair{x1, x2, x3}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush(V.JPair{x1, x2, x3}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon(V.JPair{x1, x2, x3}, V.WObj{})}, bad),
        close_obj_comma(ppush(V.JPair{x1, x2, x3}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush(V.JPair{x1, x2, x3},
          V.JNil{}), V.JNil{}), canon(V.JPair{x1, x2, x3}, V.WObj{}), rev_ppush(V.JPair{x1, x2, x3}, V.JNil{})))
    case V.JSpan{+x1, +x2}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush(V.JSpan{x1, x2}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush(V.JSpan{x1, x2}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon(V.JSpan{x1, x2}, V.WObj{})}, bad),
        close_obj_comma(ppush(V.JSpan{x1, x2}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush(V.JSpan{x1, x2},
          V.JNil{}), V.JNil{}), canon(V.JSpan{x1, x2}, V.WObj{}), rev_ppush(V.JSpan{x1, x2}, V.JNil{})))
    case V.JBind{+x1, +x2, +x3, +x4}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush(V.JBind{x1, x2, x3, x4}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush(V.JBind{x1, x2, x3, x4},
        V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon(V.JBind{x1, x2, x3, x4}, V.WObj{})}, bad),
        close_obj_comma(ppush(V.JBind{x1, x2, x3, x4}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush(V.JBind{x1, x2, x3,
          x4}, V.JNil{}), V.JNil{}), canon(V.JBind{x1, x2, x3, x4}, V.WObj{}), rev_ppush(V.JBind{x1, x2, x3, x4},
          V.JNil{})))

# what pv says of a value by its shape: at a place a value may go, a value's
# tokens put the value; an array's or object's cells push their elements
def pg(
  +val: V.Json,
  sh: V.Shape,
  +bad: Bool,
  +root: Maybe<&2, V.Json>,
  +stk: List<&2, Parse.Frame>,
  +acc: V.Json
) -> Type:
  match sh:
    case V.WVal{}:
      {Parse.step.ready(stk, root) == True{} : Bool} ->
        {Parse.run(tj(val, V.WVal{}), Parse.P{bad, root, stk}) == Parse.put(stk, root, canon(val, V.WVal{}),
          bad) : Parse.P}
    case V.WArr{}:
      {Parse.run(tj(val, V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}) ==
        Parse.P{bad, root, Parse.FArr{rpush(val, acc), aslot(val)} <> stk} : Parse.P}
    case V.WObj{}:
      {Parse.run(tj(val, V.WObj{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{""}, Parse.SKey{}} <> stk}) ==
        Parse.P{bad, root, Parse.FObj{ppush(val, acc), Parse.KOwn{""}, oslot(val)} <> stk} : Parse.P}

# pv for a boolean
law pv_bool:
  for bb: Bool
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  pg(V.JBool{bb}, V.WVal{}, bad, root, stk, V.JNil{})

def pv_bool(bb, _bad, _root, _stk):
  match bb:
    case True{}:
      _hr => {==}
    case False{}:
      _hr => {==}

# pv for an array cell, by what follows it
law pv_cons:
  for tl: V.Json
  for +hd: V.Json
  for +h: {V.wf.go(V.JCons{hd, tl}, V.WArr{}) == True{} : Bool}
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +acc: V.Json
  for ih_hd: {V.wf.go(hd, V.WVal{}) == True{} : Bool} -> pg(hd, V.WVal{}, bad, root, Parse.FArr{acc,
    Parse.SValue{}} <> stk, V.JNil{})
  for ih_tl: {V.wf.go(tl, V.WArr{}) == True{} : Bool} -> pg(tl, V.WArr{}, bad, root, stk, V.JCons{canon(hd, V.WVal{}),
    acc})
  pg(V.JCons{hd, tl}, V.WArr{}, bad, root, stk, acc)

def pv_cons(tl, hd, h, bad, root, stk, acc, ih_hd, ih_tl):
  match tl:
    case V.JNil{}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNil{}, V.WArr{}), h)
      ih_hd(hd_ok)({==})
    case V.JNull{}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNull{}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNull{}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JNull{},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JNull{}, V.WArr{}), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush(V.JNull{}, V.JCons{canon(hd,
        V.WVal{}), acc}), aslot(V.JNull{})} <> stk}, prun_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JNull{},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JNull{}, V.WArr{}), Parse.run(tj(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JNull{},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush(V.JNull{}, V.JCons{canon(hd, V.WVal{}), acc}), aslot(V.JNull{})} <> stk},
          Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JNull{}, V.WArr{}), zz), Parse.run(tj(hd,
          V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JBool{+x1}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBool{x1}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBool{x1}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JBool{x1},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JBool{x1}, V.WArr{}), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush(V.JBool{x1}, V.JCons{canon(hd,
        V.WVal{}), acc}), aslot(V.JBool{x1})} <> stk}, prun_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JBool{x1},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JBool{x1}, V.WArr{}), Parse.run(tj(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JBool{x1},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush(V.JBool{x1}, V.JCons{canon(hd, V.WVal{}), acc}),
          aslot(V.JBool{x1})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JBool{x1},
          V.WArr{}), zz), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JNum{+x1}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNum{x1}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNum{x1}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JNum{x1},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JNum{x1}, V.WArr{}), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush(V.JNum{x1}, V.JCons{canon(hd,
        V.WVal{}), acc}), aslot(V.JNum{x1})} <> stk}, prun_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JNum{x1},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JNum{x1}, V.WArr{}), Parse.run(tj(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JNum{x1},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush(V.JNum{x1}, V.JCons{canon(hd, V.WVal{}), acc}),
          aslot(V.JNum{x1})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JNum{x1},
          V.WArr{}), zz), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JStr{+x1}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JStr{x1}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JStr{x1}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JStr{x1},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JStr{x1}, V.WArr{}), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush(V.JStr{x1}, V.JCons{canon(hd,
        V.WVal{}), acc}), aslot(V.JStr{x1})} <> stk}, prun_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JStr{x1},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JStr{x1}, V.WArr{}), Parse.run(tj(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JStr{x1},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush(V.JStr{x1}, V.JCons{canon(hd, V.WVal{}), acc}),
          aslot(V.JStr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JStr{x1},
          V.WArr{}), zz), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JArr{+x1}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JArr{x1}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JArr{x1}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JArr{x1},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JArr{x1}, V.WArr{}), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush(V.JArr{x1}, V.JCons{canon(hd,
        V.WVal{}), acc}), aslot(V.JArr{x1})} <> stk}, prun_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JArr{x1},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JArr{x1}, V.WArr{}), Parse.run(tj(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JArr{x1},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush(V.JArr{x1}, V.JCons{canon(hd, V.WVal{}), acc}),
          aslot(V.JArr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JArr{x1},
          V.WArr{}), zz), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JObj{+x1}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JObj{x1}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JObj{x1}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JObj{x1},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JObj{x1}, V.WArr{}), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush(V.JObj{x1}, V.JCons{canon(hd,
        V.WVal{}), acc}), aslot(V.JObj{x1})} <> stk}, prun_app(tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JObj{x1},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JObj{x1}, V.WArr{}), Parse.run(tj(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JObj{x1},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush(V.JObj{x1}, V.JCons{canon(hd, V.WVal{}), acc}),
          aslot(V.JObj{x1})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JObj{x1},
          V.WArr{}), zz), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JCons{+x1, +x2}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JCons{x1, x2},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WArr{}), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush(V.JCons{x1, x2},
        V.JCons{canon(hd, V.WVal{}), acc}), aslot(V.JCons{x1, x2})} <> stk}, prun_app(tj(hd, V.WVal{}),
        Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WArr{}), Parse.run(tj(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush(V.JCons{x1, x2}, V.JCons{canon(hd, V.WVal{}), acc}), aslot(V.JCons{x1,
          x2})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WArr{}),
          zz), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}), Parse.P{bad,
          root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JPair{+x1, +x2, +x3}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JPair{x1, x2, x3},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2, x3}, V.WArr{}), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush(V.JPair{x1, x2, x3},
        V.JCons{canon(hd, V.WVal{}), acc}), aslot(V.JPair{x1, x2, x3})} <> stk}, prun_app(tj(hd, V.WVal{}),
        Lex.TComma{} <> tj(V.JPair{x1, x2, x3}, V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2, x3}, V.WArr{}), Parse.run(tj(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2,
          x3}, V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush(V.JPair{x1, x2, x3}, V.JCons{canon(hd, V.WVal{}), acc}),
          aslot(V.JPair{x1, x2, x3})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2, x3}, V.WArr{}), zz), Parse.run(tj(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd,
          V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JSpan{+x1, +x2}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{x1, x2},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WArr{}), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush(V.JSpan{x1, x2},
        V.JCons{canon(hd, V.WVal{}), acc}), aslot(V.JSpan{x1, x2})} <> stk}, prun_app(tj(hd, V.WVal{}),
        Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WArr{}), Parse.run(tj(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush(V.JSpan{x1, x2}, V.JCons{canon(hd, V.WVal{}), acc}), aslot(V.JSpan{x1,
          x2})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WArr{}),
          zz), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}), Parse.P{bad,
          root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JBind{+x1, +x2, +x3, +x4}:
      hd_ok = stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WArr{}), h)
      tl_ok = stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(V.JBind{x1, x2, x3,
        x4}, V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WArr{}), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush(V.JBind{x1, x2, x3, x4},
        V.JCons{canon(hd, V.WVal{}), acc}), aslot(V.JBind{x1, x2, x3, x4})} <> stk}, prun_app(tj(hd, V.WVal{}),
        Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WArr{}), Parse.P{bad, root, Parse.FArr{acc,
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WArr{}), Parse.run(tj(hd,
          V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WArr{}), Parse.P{bad, root,
          Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}), Parse.P{bad, root,
          Parse.FArr{rpush(V.JBind{x1, x2, x3, x4}, V.JCons{canon(hd, V.WVal{}), acc}), aslot(V.JBind{x1, x2, x3,
          x4})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4},
          V.WArr{}), zz), Parse.run(tj(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))

# pv for an object cell, by what follows it
law pv_pair:
  for rr: V.Json
  for +kk: String
  for +vv: V.Json
  for +h: {V.wf.go(V.JPair{kk, vv, rr}, V.WObj{}) == True{} : Bool}
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +acc: V.Json
  for ih_v: {V.wf.go(vv, V.WVal{}) == True{} : Bool} -> pg(vv, V.WVal{}, bad, root, Parse.FObj{acc,
    Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk, V.JNil{})
  for ih_r: {V.wf.go(rr, V.WObj{}) == True{} : Bool} -> pg(rr, V.WObj{}, bad, root, stk,
    V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc})
  pg(V.JPair{kk, vv, rr}, V.WObj{}, bad, root, stk, acc)

def pv_pair(rr, kk, vv, h, bad, root, stk, acc, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h)
      ih_v(v_ok)({==})
    case V.JNull{}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNull{},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JNull{}, V.WObj{}), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush(V.JNull{}, V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JNull{})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNull{}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JNull{}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> tj(V.JNull{}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JNull{}, V.JPair{fixs(String.to_list(kk)),
          canon(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JNull{})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JNull{}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
          Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JBool{+x1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{x1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBool{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JBool{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush(V.JBool{x1}, V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JBool{x1})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBool{x1}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JBool{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> tj(V.JBool{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JBool{x1}, V.JPair{fixs(String.to_list(kk)),
          canon(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JBool{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JBool{x1}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad,
          root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JNum{+x1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{x1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNum{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JNum{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush(V.JNum{x1}, V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JNum{x1})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNum{x1}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JNum{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> tj(V.JNum{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JNum{x1}, V.JPair{fixs(String.to_list(kk)),
          canon(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JNum{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JNum{x1}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
          Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JStr{+x1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{x1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JStr{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JStr{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush(V.JStr{x1}, V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JStr{x1})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JStr{x1}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JStr{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> tj(V.JStr{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JStr{x1}, V.JPair{fixs(String.to_list(kk)),
          canon(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JStr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JStr{x1}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
          Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JArr{+x1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{x1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JArr{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JArr{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush(V.JArr{x1}, V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JArr{x1})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JArr{x1}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JArr{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> tj(V.JArr{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JArr{x1}, V.JPair{fixs(String.to_list(kk)),
          canon(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JArr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JArr{x1}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
          Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JObj{+x1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{x1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JObj{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JObj{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush(V.JObj{x1}, V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JObj{x1})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JObj{x1}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JObj{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> tj(V.JObj{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JObj{x1}, V.JPair{fixs(String.to_list(kk)),
          canon(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JObj{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JObj{x1}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
          Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JCons{+x1, +x2}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JCons{x1, x2},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WObj{}), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush(V.JCons{x1, x2}, V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JCons{x1, x2})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WObj{}),
        Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JCons{x1, x2},
          V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JCons{x1,
          x2})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WObj{}),
          zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv,
          V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JPair{+x1, +x2, +x3}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JPair{x1, x2, x3},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2, x3}, V.WObj{}), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush(V.JPair{x1, x2, x3}, V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}),
        Parse.KOwn{""}, oslot(V.JPair{x1, x2, x3})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JPair{x1,
        x2, x3}, V.WObj{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2, x3}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2, x3}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JPair{x1, x2, x3},
          V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JPair{x1, x2,
          x3})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2, x3},
          V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc,
          Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JSpan{+x1, +x2}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{x1, x2},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WObj{}), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush(V.JSpan{x1, x2}, V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JSpan{x1, x2})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WObj{}),
        Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JSpan{x1, x2},
          V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JSpan{x1,
          x2})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WObj{}),
          zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv,
          V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JBind{+x1, +x2, +x3, +x4}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBind{x1, x2, x3,
        x4}, V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))},
        Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WObj{}), Parse.run(tj(vv,
        V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk})),
        Parse.P{bad, root, Parse.FObj{ppush(V.JBind{x1, x2, x3, x4}, V.JPair{fixs(String.to_list(kk)), canon(vv,
        V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JBind{x1, x2, x3, x4})} <> stk}, prun_app(tj(vv, V.WVal{}),
        Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WObj{}), Parse.P{bad, root, Parse.FObj{acc,
        Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WObj{}), Parse.run(tj(vv,
          V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WObj{}), Parse.P{bad,
          root, Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JBind{x1, x2, x3, x4},
          V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JBind{x1, x2, x3,
          x4})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4},
          V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc,
          Parse.KOwn{fixs(String.to_list(kk))}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))

# pv for an object cell, by what follows it
law pv_bind:
  for rr: V.Json
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for +h: {V.wf.go(V.JBind{src, nn, vv, rr}, V.WObj{}) == True{} : Bool}
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +acc: V.Json
  for ih_v: {V.wf.go(vv, V.WVal{}) == True{} : Bool} -> pg(vv, V.WVal{}, bad, root, Parse.FObj{acc,
    Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk, V.JNil{})
  for ih_r: {V.wf.go(rr, V.WObj{}) == True{} : Bool} -> pg(rr, V.WObj{}, bad, root, stk,
    V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc})
  pg(V.JBind{src, nn, vv, rr}, V.WObj{}, bad, root, stk, acc)

def pv_bind(rr, src, nn, vv, h, bad, root, stk, acc, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h)
      ih_v(v_ok)({==})
    case V.JNull{}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNull{},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> tj(V.JNull{}, V.WObj{}),
        Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src,
        nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush(V.JNull{},
        V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JNull{})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNull{}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JNull{}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JNull{}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JNull{},
          V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JNull{})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JNull{}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
          Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JBool{+x1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{x1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBool{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> tj(V.JBool{x1}, V.WObj{}),
        Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src,
        nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush(V.JBool{x1},
        V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JBool{x1})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBool{x1}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JBool{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JBool{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JBool{x1},
          V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JBool{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JBool{x1}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad,
          root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JNum{+x1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{x1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNum{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> tj(V.JNum{x1}, V.WObj{}),
        Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src,
        nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush(V.JNum{x1},
        V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JNum{x1})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JNum{x1}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JNum{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JNum{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JNum{x1},
          V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JNum{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JNum{x1}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
          Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JStr{+x1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{x1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JStr{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> tj(V.JStr{x1}, V.WObj{}),
        Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src,
        nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush(V.JStr{x1},
        V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JStr{x1})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JStr{x1}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JStr{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JStr{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JStr{x1},
          V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JStr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JStr{x1}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
          Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JArr{+x1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{x1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JArr{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> tj(V.JArr{x1}, V.WObj{}),
        Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src,
        nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush(V.JArr{x1},
        V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JArr{x1})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JArr{x1}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JArr{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JArr{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JArr{x1},
          V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JArr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JArr{x1}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
          Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JObj{+x1}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{x1}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JObj{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> tj(V.JObj{x1}, V.WObj{}),
        Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src,
        nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush(V.JObj{x1},
        V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JObj{x1})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JObj{x1}, V.WObj{}), Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JObj{x1}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JObj{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JObj{x1},
          V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JObj{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JObj{x1}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root,
          Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JCons{+x1, +x2}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JCons{x1, x2},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WObj{}),
        Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src,
        nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush(V.JCons{x1, x2},
        V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JCons{x1, x2})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WObj{}),
        Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JCons{x1, x2},
          V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JCons{x1, x2})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JCons{x1, x2}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad,
          root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JPair{+x1, +x2, +x3}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JPair{x1, x2, x3},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2, x3}, V.WObj{}),
        Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src,
        nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush(V.JPair{x1, x2, x3},
        V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JPair{x1, x2, x3})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JPair{x1, x2, x3},
        V.WObj{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2, x3}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2, x3}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JPair{x1, x2, x3},
          V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JPair{x1, x2, x3})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JPair{x1, x2, x3}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JSpan{+x1, +x2}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{x1, x2},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WObj{}),
        Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src,
        nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush(V.JSpan{x1, x2},
        V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JSpan{x1, x2})} <> stk}, prun_app(tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WObj{}),
        Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WObj{}), Parse.run(tj(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(V.JSpan{x1, x2},
          V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JSpan{x1, x2})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> tj(V.JSpan{x1, x2}, V.WObj{}), zz), Parse.run(tj(vv, V.WVal{}), Parse.P{bad,
          root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JBind{+x1, +x2, +x3, +x4}:
      v_ok = stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WObj{}), h)
      r_ok = stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(V.JBind{x1, x2, x3,
        x4}, V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WObj{}),
        Parse.run(tj(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src,
        nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush(V.JBind{x1, x2, x3,
        x4}, V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}),
        Parse.KOwn{""}, oslot(V.JBind{x1, x2, x3, x4})} <> stk}, prun_app(tj(vv, V.WVal{}),
        Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WObj{}), Parse.P{bad, root, Parse.FObj{acc,
        Parse.KOwn{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WObj{}), Parse.run(tj(vv,
          V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))}, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4},
          V.WObj{}), Parse.P{bad, root, Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))),
          canon(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{ppush(V.JBind{x1, x2, x3, x4}, V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))),
          canon(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JBind{x1, x2, x3, x4})} <> stk}, Equal.cong(Parse.P,
          Parse.P, zz => Parse.run(Lex.TComma{} <> tj(V.JBind{x1, x2, x3, x4}, V.WObj{}), zz), Parse.run(tj(vv,
          V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))

# the parser on a well-formed value's tokens
law pv:
  for +val: V.Json
  for +sh: V.Shape
  for +h: {V.wf.go(val, sh) == True{} : Bool}
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +acc: V.Json
  pg(val, sh, bad, root, stk, acc)

def pv(val, sh, h, bad, root, stk, acc):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          _hr => {==}
        case V.WArr{}:
          no(pg(V.JNull{}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          no(pg(V.JNull{}, V.WObj{}, bad, root, stk, acc), h)
    case V.JBool{bb}:
      match sh:
        case V.WVal{}:
          pv_bool(bb, bad, root, stk)
        case V.WArr{}:
          no(pg(V.JBool{bb}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          no(pg(V.JBool{bb}, V.WObj{}, bad, root, stk, acc), h)
    case V.JNum{+raw}:
      match sh:
        case V.WVal{}:
          _hr => step_num(raw, h, bad, root, stk)
        case V.WArr{}:
          no(pg(V.JNum{raw}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          no(pg(V.JNum{raw}, V.WObj{}, bad, root, stk, acc), h)
    case V.JStr{+txt}:
      match sh:
        case V.WVal{}:
          hr => put_str_ready(stk, root, fixs(String.to_list(txt)), bad, hr)
        case V.WArr{}:
          no(pg(V.JStr{txt}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          no(pg(V.JStr{txt}, V.WObj{}, bad, root, stk, acc), h)
    case V.JArr{+items}:
      match sh:
        case V.WVal{}:
          hr =>
            Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(items, V.WArr{}), [Lex.TCloseArr{}]),
              Parse.step.open_arr(Parse.P{bad, root, stk})), Parse.run(List.append(&2, Lex.Tok, tj(items, V.WArr{}),
              [Lex.TCloseArr{}]), Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk}), Parse.put(stk,
              root, V.JArr{canon(items, V.WArr{})}, bad), Equal.cong(Parse.P, Parse.P, zz => Parse.run(List.append(&2,
              Lex.Tok, tj(items, V.WArr{}), [Lex.TCloseArr{}]), zz), Parse.step.open_arr(Parse.P{bad, root, stk}),
              Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk}, open_arr_ready(bad, root, stk, hr)),
              Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(items, V.WArr{}), [Lex.TCloseArr{}]),
                Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk}), Parse.run([Lex.TCloseArr{}],
                Parse.run(tj(items, V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk})),
                Parse.put(stk, root, V.JArr{canon(items, V.WArr{})}, bad), prun_app(tj(items, V.WArr{}),
                [Lex.TCloseArr{}], Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk}),
              Equal.trans(Parse.P, Parse.run([Lex.TCloseArr{}], Parse.run(tj(items, V.WArr{}), Parse.P{bad, root,
                Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk})), Parse.run([Lex.TCloseArr{}], Parse.P{bad, root,
                Parse.FArr{rpush(items, V.JNil{}), aslot(items)} <> stk}), Parse.put(stk, root, V.JArr{canon(items,
                V.WArr{})}, bad), Equal.cong(Parse.P, Parse.P, zz => Parse.run([Lex.TCloseArr{}], zz),
                Parse.run(tj(items, V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk}),
                Parse.P{bad, root, Parse.FArr{rpush(items, V.JNil{}), aslot(items)} <> stk}, pv(items, V.WArr{}, h,
                bad, root, stk, V.JNil{})),
              close_after_arr(items, bad, root, stk))))
        case V.WArr{}:
          no(pg(V.JArr{items}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          no(pg(V.JArr{items}, V.WObj{}, bad, root, stk, acc), h)
    case V.JObj{+pairs}:
      match sh:
        case V.WVal{}:
          hr =>
            Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(pairs, V.WObj{}), [Lex.TCloseObj{}]),
              Parse.step.open_obj(Parse.P{bad, root, stk})), Parse.run(List.append(&2, Lex.Tok, tj(pairs, V.WObj{}),
              [Lex.TCloseObj{}]), Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""}, Parse.SKey{}} <> stk}),
              Parse.put(stk, root, V.JObj{canon(pairs, V.WObj{})}, bad), Equal.cong(Parse.P, Parse.P,
              zz => Parse.run(List.append(&2, Lex.Tok, tj(pairs, V.WObj{}), [Lex.TCloseObj{}]), zz),
              Parse.step.open_obj(Parse.P{bad, root, stk}), Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""},
              Parse.SKey{}} <> stk}, open_obj_ready(bad, root, stk, hr)),
              Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, tj(pairs, V.WObj{}), [Lex.TCloseObj{}]),
                Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""}, Parse.SKey{}} <> stk}),
                Parse.run([Lex.TCloseObj{}], Parse.run(tj(pairs, V.WObj{}), Parse.P{bad, root, Parse.FObj{V.JNil{},
                Parse.KOwn{""}, Parse.SKey{}} <> stk})), Parse.put(stk, root, V.JObj{canon(pairs, V.WObj{})}, bad),
                prun_app(tj(pairs, V.WObj{}), [Lex.TCloseObj{}], Parse.P{bad, root, Parse.FObj{V.JNil{},
                Parse.KOwn{""}, Parse.SKey{}} <> stk}),
              Equal.trans(Parse.P, Parse.run([Lex.TCloseObj{}], Parse.run(tj(pairs, V.WObj{}), Parse.P{bad, root,
                Parse.FObj{V.JNil{}, Parse.KOwn{""}, Parse.SKey{}} <> stk})), Parse.run([Lex.TCloseObj{}], Parse.P{bad,
                root, Parse.FObj{ppush(pairs, V.JNil{}), Parse.KOwn{""}, oslot(pairs)} <> stk}), Parse.put(stk, root,
                V.JObj{canon(pairs, V.WObj{})}, bad), Equal.cong(Parse.P, Parse.P, zz => Parse.run([Lex.TCloseObj{}],
                zz), Parse.run(tj(pairs, V.WObj{}), Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""},
                Parse.SKey{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush(pairs, V.JNil{}), Parse.KOwn{""},
                oslot(pairs)} <> stk}, pv(pairs, V.WObj{}, h, bad, root, stk, V.JNil{})),
              close_after_obj(pairs, bad, root, stk))))
        case V.WArr{}:
          no(pg(V.JObj{pairs}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          no(pg(V.JObj{pairs}, V.WObj{}, bad, root, stk, acc), h)
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          no(pg(V.JNil{}, V.WVal{}, bad, root, stk, acc), h)
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JCons{+hd, +tl}:
      match sh:
        case V.WVal{}:
          no(pg(V.JCons{hd, tl}, V.WVal{}, bad, root, stk, acc), h)
        case V.WArr{}:
          pv_cons(tl, hd, h, bad, root, stk, acc, xx => pv(hd, V.WVal{}, xx, bad, root, Parse.FArr{acc,
            Parse.SValue{}} <> stk, V.JNil{}),
            xx => pv(tl, V.WArr{}, xx, bad, root, stk, V.JCons{canon(hd, V.WVal{}), acc}))
        case V.WObj{}:
          no(pg(V.JCons{hd, tl}, V.WObj{}, bad, root, stk, acc), h)
    case V.JPair{+kk, +vv, +rr}:
      match sh:
        case V.WVal{}:
          no(pg(V.JPair{kk, vv, rr}, V.WVal{}, bad, root, stk, acc), h)
        case V.WArr{}:
          no(pg(V.JPair{kk, vv, rr}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          pv_pair(rr, kk, vv, h, bad, root, stk, acc,
            xx => pv(vv, V.WVal{}, xx, bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(kk))},
              Parse.SValue{}} <> stk, V.JNil{}),
            xx => pv(rr, V.WObj{}, xx, bad, root, stk, V.JPair{fixs(String.to_list(kk)), canon(vv, V.WVal{}), acc}))
    case V.JSpan{+src, +nn}:
      match sh:
        case V.WVal{}:
          hr => put_str_ready(stk, root, fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), bad, hr)
        case V.WArr{}:
          no(pg(V.JSpan{src, nn}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          no(pg(V.JSpan{src, nn}, V.WObj{}, bad, root, stk, acc), h)
    case V.JBind{+src, +nn, +vv, +rr}:
      match sh:
        case V.WVal{}:
          no(pg(V.JBind{src, nn, vv, rr}, V.WVal{}, bad, root, stk, acc), h)
        case V.WArr{}:
          no(pg(V.JBind{src, nn, vv, rr}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          pv_bind(rr, src, nn, vv, h, bad, root, stk, acc,
            xx => pv(vv, V.WVal{}, xx, bad, root, Parse.FObj{acc, Parse.KOwn{fixs(String.to_list(V.span.str(src, nn,
              U32.is_zero(nn))))}, Parse.SValue{}} <> stk, V.JNil{}),
            xx => pv(rr, V.WObj{}, xx, bad, root, stk, V.JPair{fixs(String.to_list(V.span.str(src, nn,
              U32.is_zero(nn)))), canon(vv, V.WVal{}), acc}))

# WP-P1: parse on a well-formed value's tokens gives the value back, strings
# owned and fixed
law parse_tj:
  for +val: V.Json
  for h_wf: {V.wf(val) == True{} : Bool}
  {Parse.finish(Parse.run(tj(val, V.WVal{}), Parse.P{False{}, None{}, Nil{}})) == Some{canon(val,
    V.WVal{})} : Maybe<&2, V.Json>}

def parse_tj(val, h_wf):
  Equal.cong(Parse.P, Maybe<&2, V.Json>, zz => Parse.finish(zz), Parse.run(tj(val, V.WVal{}), Parse.P{False{}, None{},
    Nil{}}),
    Parse.P{False{}, Some{canon(val, V.WVal{})}, Nil{}}, pv(val, V.WVal{}, h_wf, False{}, None{}, Nil{},
      V.JNil{})({==}))

# JSON-PRINT-3, the parse half: parse's state only ever holds well-formed values

# a finished root is well-formed
def minv(root: Maybe<&2, V.Json>) -> Type:
  match root:
    case None{}:
      Unit
    case Some{jj}:
      {V.wf(jj) == True{} : Bool}

# an open frame's cells are well-formed
def frinv(fr: Parse.Frame) -> Type:
  match fr:
    case Parse.FArr{items, _}:
      {V.wf.go(items, V.WArr{}) == True{} : Bool}
    case Parse.FObj{pairs, _, _}:
      {V.wf.go(pairs, V.WObj{}) == True{} : Bool}

# every open frame's cells are well-formed
def finv(stk: List<&2, Parse.Frame>) -> Type:
  match stk:
    case Nil{}:
      Unit
    case fr <> rest:
      (frinv(fr) & finv(rest))

# the parser's state holds only well-formed values
def pinv(st: Parse.P) -> Type:
  match st:
    case Parse.P{_bad, root, stk}:
      (minv(root) & finv(stk))

# a well-formed value in front of well-formed cells
law cons_wf:
  for +vv: V.Json
  for +items: V.Json
  for hv: {V.wf(vv) == True{} : Bool}
  for hi: {V.wf.go(items, V.WArr{}) == True{} : Bool}
  {V.wf.go(V.JCons{vv, items}, V.WArr{}) == True{} : Bool}

def cons_wf(vv, items, hv, hi):
  hs = Equal.sym(Bool, V.wf(vv), True{}, hv)
  %hs : {Lazy.stop(Bool, Bool.not(_), False{}, _u => V.wf.go(items, V.WArr{})) == True{} : Bool}
  hi

# a well-formed value under a key, in front of well-formed cells
law pair_wf:
  for key: Parse.Key
  for +vv: V.Json
  for +pairs: V.Json
  for hv: {V.wf(vv) == True{} : Bool}
  for hp: {V.wf.go(pairs, V.WObj{}) == True{} : Bool}
  {V.wf.go(Parse.put.pair(key, vv, pairs), V.WObj{}) == True{} : Bool}

def pair_wf(key, vv, pairs, hv, hp):
  match key:
    case Parse.KOwn{_txt}:
      hs = Equal.sym(Bool, V.wf(vv), True{}, hv)
      %hs : {Lazy.stop(Bool, Bool.not(_), False{}, _u => V.wf.go(pairs, V.WObj{})) == True{} : Bool}
      hp
    case Parse.KCut{_src, _nn}:
      hs = Equal.sym(Bool, V.wf(vv), True{}, hv)
      %hs : {Lazy.stop(Bool, Bool.not(_), False{}, _u => V.wf.go(pairs, V.WObj{})) == True{} : Bool}
      hp

# a string key's text is well-formed
law text_wf:
  for key: Parse.Key
  {V.wf(Parse.put.text(key)) == True{} : Bool}

def text_wf(key):
  match key:
    case Parse.KOwn{_txt}:
      {==}
    case Parse.KCut{_src, _nn}:
      {==}

# well-formed array cells reversed onto well-formed cells
law rev_wf_arr:
  for +cells: V.Json
  for +acc: V.Json
  for +hc: {V.wf.go(cells, V.WArr{}) == True{} : Bool}
  for ha: {V.wf.go(acc, V.WArr{}) == True{} : Bool}
  {V.wf.go(V.reverse(cells, acc), V.WArr{}) == True{} : Bool}

def rev_wf_arr(cells, acc, hc, ha):
  match cells:
    case V.JNull{}:
      no({V.wf.go(V.reverse(V.JNull{}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JBool{+x1}:
      no({V.wf.go(V.reverse(V.JBool{x1}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JNum{+x1}:
      no({V.wf.go(V.reverse(V.JNum{x1}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JStr{+x1}:
      no({V.wf.go(V.reverse(V.JStr{x1}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JArr{+x1}:
      no({V.wf.go(V.reverse(V.JArr{x1}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JObj{+x1}:
      no({V.wf.go(V.reverse(V.JObj{x1}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JNil{}:
      ha
    case V.JCons{+x1, +x2}:
      rev_wf_arr(x2, V.JCons{x1, acc}, stop_r(V.wf(x1), V.wf.go(x2, V.WArr{}), hc),
        cons_wf(x1, acc, stop_l(V.wf(x1), V.wf.go(x2, V.WArr{}), hc), ha))
    case V.JPair{+x1, +x2, +x3}:
      no({V.wf.go(V.reverse(V.JPair{x1, x2, x3}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JSpan{+x1, +x2}:
      no({V.wf.go(V.reverse(V.JSpan{x1, x2}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JBind{+x1, +x2, +x3, +x4}:
      no({V.wf.go(V.reverse(V.JBind{x1, x2, x3, x4}, acc), V.WArr{}) == True{} : Bool}, hc)

# well-formed object cells reversed onto well-formed cells
law rev_wf_obj:
  for +cells: V.Json
  for +acc: V.Json
  for +hc: {V.wf.go(cells, V.WObj{}) == True{} : Bool}
  for ha: {V.wf.go(acc, V.WObj{}) == True{} : Bool}
  {V.wf.go(V.reverse(cells, acc), V.WObj{}) == True{} : Bool}

def rev_wf_obj(cells, acc, hc, ha):
  match cells:
    case V.JNull{}:
      no({V.wf.go(V.reverse(V.JNull{}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JBool{+x1}:
      no({V.wf.go(V.reverse(V.JBool{x1}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JNum{+x1}:
      no({V.wf.go(V.reverse(V.JNum{x1}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JStr{+x1}:
      no({V.wf.go(V.reverse(V.JStr{x1}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JArr{+x1}:
      no({V.wf.go(V.reverse(V.JArr{x1}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JObj{+x1}:
      no({V.wf.go(V.reverse(V.JObj{x1}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JNil{}:
      ha
    case V.JCons{+x1, +x2}:
      no({V.wf.go(V.reverse(V.JCons{x1, x2}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JPair{+x1, +x2, +x3}:
      rev_wf_obj(x3, V.JPair{x1, x2, acc}, stop_r(V.wf(x2), V.wf.go(x3, V.WObj{}), hc),
        pair_wf(Parse.KOwn{x1}, x2, acc, stop_l(V.wf(x2), V.wf.go(x3, V.WObj{}), hc), ha))
    case V.JSpan{+x1, +x2}:
      no({V.wf.go(V.reverse(V.JSpan{x1, x2}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JBind{+x1, +x2, +x3, +x4}:
      rev_wf_obj(x4, V.JBind{x1, x2, x3, acc}, stop_r(V.wf(x3), V.wf.go(x4, V.WObj{}), hc),
        pair_wf(Parse.KCut{x1, x2}, x3, acc, stop_l(V.wf(x3), V.wf.go(x4, V.WObj{}), hc), ha))

# put keeps the state well-formed, given a well-formed value
law put_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +vv: V.Json
  for +bad: Bool
  for hv: {V.wf(vv) == True{} : Bool}
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.put(stk, root, vv, bad))

def put_inv(stk, root, vv, _bad, hv, h):
  match stk:
    case Nil{}:
      match root:
        case None{}:
          (hv, Unit{})
        case Some{_rr}:
          (hr, _hs) = h
          (hr, Unit{})
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, (hf, hrest)) = h
              (hr, (cons_wf(vv, items, hv, hf), hrest))
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})
        case Parse.FObj{+pairs, +key, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, (hf, hrest)) = h
              (hr, (pair_wf(key, vv, pairs, hv, hf), hrest))
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})
# a colon keeps the state well-formed
law colon_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.colon(stk, root, bad))

def colon_inv(stk, _root, _bad, h):
  match stk:
    case Nil{}:
      (hr, _rest) = h
      (hr, Unit{})
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})
        case Parse.FObj{+pairs, +key, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              h

# a comma keeps the state well-formed
law comma_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.comma(stk, root, bad))

def comma_inv(stk, _root, _bad, h):
  match stk:
    case Nil{}:
      (hr, _rest) = h
      (hr, Unit{})
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              h
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})
        case Parse.FObj{+pairs, +key, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              h
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})

# a string keeps the state well-formed
law str_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +key: Parse.Key
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.put.str(stk, root, key, bad))

def str_inv(stk, root, key, bad, h):
  match stk:
    case Nil{}:
      put_inv([], root, Parse.put.text(key), bad, text_wf(key), h)
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, slot}:
          match slot:
            case Parse.SValue{}:
              put_inv(Parse.FArr{items, Parse.SValue{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
            case Parse.SComma{}:
              put_inv(Parse.FArr{items, Parse.SComma{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
            case Parse.SKey{}:
              put_inv(Parse.FArr{items, Parse.SKey{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
            case Parse.SColon{}:
              put_inv(Parse.FArr{items, Parse.SColon{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
        case Parse.FObj{+pairs, +k2, slot}:
          match slot:
            case Parse.SValue{}:
              put_inv(Parse.FObj{pairs, k2, Parse.SValue{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
            case Parse.SComma{}:
              put_inv(Parse.FObj{pairs, k2, Parse.SComma{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
            case Parse.SKey{}:
              h
            case Parse.SColon{}:
              put_inv(Parse.FObj{pairs, k2, Parse.SColon{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)

# close_arr_inv, for one frame
law ca_arr:
  for slot: Parse.Slot
  for items: V.Json
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, Parse.FArr{items, slot} <> rest})
  pinv(Parse.close_arr(Parse.FArr{items, slot} <> rest, root, bad))

def ca_arr(slot, items, rest, root, bad, h):
  match slot:
    case Parse.SValue{}:
      match items:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, (_hf, hrest)) = h
          put_inv(rest, root, V.JArr{V.JNil{}}, bad, {==}, (hr, hrest))
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})
    case Parse.SComma{}:
      (hr, (hf, hrest)) = h
      +it = items
      ec = Equal.sym(Parse.P, Parse.close_arr(Parse.FArr{it, Parse.SComma{}} <> rest, root, bad),
        Parse.put(rest, root, V.JArr{V.reverse(it, V.JNil{})}, bad), close_arr_comma(it, rest, root, bad))
      %ec : pinv(_)
      put_inv(rest, root, V.JArr{V.reverse(it, V.JNil{})}, bad, rev_wf_arr(it, V.JNil{}, hf, {==}), (hr, hrest))
    case Parse.SKey{}:
      match items:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})
    case Parse.SColon{}:
      match items:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})

# a closing bracket keeps the state well-formed
law close_arr_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.close_arr(stk, root, bad))

def close_arr_inv(stk, root, bad, h):
  match stk:
    case Nil{}:
      (hr, _rest) = h
      (hr, Unit{})
    case fr <> +rest:
      match fr:
        case Parse.FArr{items, slot}:
          ca_arr(slot, items, rest, root, bad, h)
        case Parse.FObj{+pairs, +key, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})

# close_obj_inv, for one frame
law co_obj:
  for slot: Parse.Slot
  for pairs: V.Json
  for +key: Parse.Key
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, Parse.FObj{pairs, key, slot} <> rest})
  pinv(Parse.close_obj(Parse.FObj{pairs, key, slot} <> rest, root, bad))

def co_obj(slot, pairs, key, rest, root, bad, h):
  match slot:
    case Parse.SValue{}:
      match pairs:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})
    case Parse.SComma{}:
      (hr, (hf, hrest)) = h
      +ps = pairs
      ec = Equal.sym(Parse.P, Parse.close_obj(Parse.FObj{ps, key, Parse.SComma{}} <> rest, root, bad),
        Parse.put(rest, root, V.JObj{V.reverse(ps, V.JNil{})}, bad), close_obj_comma(ps, key, rest, root, bad))
      %ec : pinv(_)
      put_inv(rest, root, V.JObj{V.reverse(ps, V.JNil{})}, bad, rev_wf_obj(ps, V.JNil{}, hf, {==}), (hr, hrest))
    case Parse.SKey{}:
      match pairs:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, (_hf, hrest)) = h
          put_inv(rest, root, V.JObj{V.JNil{}}, bad, {==}, (hr, hrest))
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})
    case Parse.SColon{}:
      match pairs:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})

# a closing brace keeps the state well-formed
law close_obj_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.close_obj(stk, root, bad))

def close_obj_inv(stk, root, bad, h):
  match stk:
    case Nil{}:
      (hr, _rest) = h
      (hr, Unit{})
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})
        case Parse.FObj{pairs, +key, slot}:
          co_obj(slot, pairs, key, rest, root, bad, h)

# opening an array keeps the state well-formed
law oa_inv:
  for ok: Bool
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.open_arr.go(bad, root, stk, ok))

def oa_inv(ok, _bad, _root, _stk, h):
  match ok:
    case True{}:
      (hr, hs) = h
      (hr, ({==}, hs))
    case False{}:
      (hr, _hs) = h
      (hr, Unit{})

# opening an object keeps the state well-formed
law oo_inv:
  for ok: Bool
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.open_obj.go(bad, root, stk, ok))

def oo_inv(ok, _bad, _root, _stk, h):
  match ok:
    case True{}:
      (hr, hs) = h
      (hr, ({==}, hs))
    case False{}:
      (hr, _hs) = h
      (hr, Unit{})

# a word parse accepts is a well-formed value
law word_wf:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +raw: String
  for eo: {Bool.or(b1, Bool.or(b2, Bool.or(b3, V.num.ok(raw)))) == True{} : Bool}
  {V.wf(Bool.pick(V.Json, b1, V.JNull{}, Bool.pick(V.Json, b2, V.JBool{True{}}, Bool.pick(V.Json, b3,
    V.JBool{False{}}, V.JNum{raw})))) == True{} : Bool}

def word_wf(b1, b2, b3, _raw, eo):
  match b1:
    case True{}:
      {==}
    case False{}:
      match b2:
        case True{}:
          {==}
        case False{}:
          match b3:
            case True{}:
              {==}
            case False{}:
              eo

# a word keeps the state well-formed
law sw_inv:
  for ok: Bool
  for +raw: String
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for eo: {Parse.word.ok(raw) == ok : Bool}
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.word.go(raw, Parse.P{bad, root, stk}, ok))

def sw_inv(ok, raw, bad, root, stk, eo, h):
  match ok:
    case True{}:
      put_inv(stk, root, Parse.word(raw), bad, word_wf(String.eq(raw, "null"), String.eq(raw, "true"),
        String.eq(raw, "false"), raw, eo), h)
    case False{}:
      h

# a number span keeps the state well-formed
law sk_inv:
  for ok: Bool
  for +raw: String
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for eo: {V.num.ok(raw) == ok : Bool}
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.span.open(Parse.P{bad, root, stk}, Parse.step.span.ok(raw, ok)))

def sk_inv(ok, raw, bad, root, stk, eo, h):
  match ok:
    case True{}:
      put_inv(stk, root, V.JNum{raw}, bad, eo, h)
    case False{}:
      h

# a word span keeps the state well-formed
law sg_inv:
  for aa: Bool
  for bb: Bool
  for cc: Bool
  for +src: String
  for +nn: U32
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.span.open(Parse.P{bad, root, stk}, Parse.step.span.go(src, nn, aa, bb, cc)))

def sg_inv(aa, bb, cc, src, nn, bad, root, stk, h):
  match aa:
    case True{}:
      put_inv(stk, root, V.JNull{}, bad, {==}, h)
    case False{}:
      match bb:
        case True{}:
          put_inv(stk, root, V.JBool{True{}}, bad, {==}, h)
        case False{}:
          match cc:
            case True{}:
              put_inv(stk, root, V.JBool{False{}}, bad, {==}, h)
            case False{}:
              +raw = V.span.str(src, nn, U32.is_zero(nn))
              sk_inv(V.num.ok(raw), raw, bad, root, stk, {==}, h)

# one token keeps the state well-formed
law step_inv:
  for tok: Lex.Tok
  for st: Parse.P
  for h: pinv(st)
  pinv(Parse.step(tok, st))

def step_inv(tok, st, h):
  match tok:
    case Lex.TOpenArr{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          oa_inv(Parse.step.ready(stk, root), bad, root, stk, h)
    case Lex.TOpenObj{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          oo_inv(Parse.step.ready(stk, root), bad, root, stk, h)
    case Lex.TCloseArr{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          close_arr_inv(stk, root, bad, h)
    case Lex.TCloseObj{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          close_obj_inv(stk, root, bad, h)
    case Lex.TColon{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          colon_inv(stk, root, bad, h)
    case Lex.TComma{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          comma_inv(stk, root, bad, h)
    case Lex.TStr{+txt}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          str_inv(stk, root, Parse.KOwn{txt}, bad, h)
    case Lex.TWord{+raw}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          sw_inv(Parse.word.ok(raw), raw, bad, root, stk, {==}, h)
    case Lex.TStrS{+src, +nn}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          str_inv(stk, root, Parse.KCut{src, nn}, bad, h)
    case Lex.TWordS{+src, +nn}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          sg_inv(V.span.eq(src, nn, "null"), V.span.eq(src, nn, "true"), V.span.eq(src, nn, "false"), src, nn, bad,
            root, stk, h)
    case Lex.TBad{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          h

# every token keeps the state well-formed
law run_inv:
  for xs: List<&2, Lex.Tok>
  for +st: Parse.P
  for h: pinv(st)
  pinv(Parse.run(xs, st))

def run_inv(xs, st, h):
  match xs:
    case Nil{}:
      h
    case +tok <> rest:
      run_inv(rest, Parse.step(tok, st), step_inv(tok, st, h))

# a finished parse of a well-formed state is well-formed
law fin_wf:
  for bad: Bool
  for stk: List<&2, Parse.Frame>
  for root: Maybe<&2, V.Json>
  for h: (minv(root) & finv(stk))
  {Laws.wf_m(Parse.result(bad, stk, root)) == True{} : Bool}

def fin_wf(bad, stk, root, h):
  match bad:
    case True{}:
      {==}
    case False{}:
      match stk:
        case +_fr <> +_rest:
          {==}
        case Nil{}:
          match root:
            case None{}:
              {==}
            case Some{_jj}:
              (hr, _hs) = h
              hr

# a finished parse is well-formed
law fin_inv:
  for st: Parse.P
  for h: pinv(st)
  {Laws.wf_m(Parse.finish(st)) == True{} : Bool}

def fin_inv(st, h):
  match st:
    case Parse.P{bad, root, stk}:
      fin_wf(bad, stk, root, h)

def Laws.parse_wf(txt):
  fin_inv(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}),
    run_inv(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}, (Unit{}, Unit{})))

