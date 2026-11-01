# proofs of laws/WhitespaceBetweenTokensIgnored.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lex.bend as Lex
import ../laws/ParsesExactlyJsonTexts.bend as L1
import ../laws/WhitespaceBetweenTokensIgnored.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ../laws/defs/Digit.bend as D2
import ../laws/defs/GrammarDerivations.bend as D3
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/CharacterClasses.bend as M2
import ./lemmas/CharacterScan.bend as M3
import ./lemmas/CursorFollowsDerivation.bend as M4
import ./lemmas/ErrorToken.bend as M5
import ./lemmas/LexemeOrder.bend as M6
import ./lemmas/LexerBuildsDerivations.bend as M7
import ./lemmas/NumberCharsAreWordChars.bend as M8
import ./lemmas/NumberDigits.bend as M9
import ./lemmas/StringTokens.bend as M10

# laws/WhitespaceBetweenTokensIgnored.bend: whitespace between tokens

# a derivation's value does not depend on its whitespace
law val_bare:
  for +gg: D3.Gv
  {L1.g.val(Laws.g.bare(gg)) == L1.g.val(gg) : V.Json}

def val_bare(gg):
  match gg:
    case D3.GWord{_a1}:
      {==}
    case D3.GStr{_a1}:
      {==}
    case D3.GArr0{_a1}:
      {==}
    case D3.GArr{_a1, +a2, _a3, +a4}:
      Equal.trans(V.Json, V.JArr{V.JCons{L1.g.val(Laws.g.bare(a2)), L1.g.val(Laws.g.bare(a4))}},
        V.JArr{V.JCons{L1.g.val(a2), L1.g.val(Laws.g.bare(a4))}}, V.JArr{V.JCons{L1.g.val(a2), L1.g.val(a4)}},
        Equal.cong(V.Json, V.Json, zz => V.JArr{V.JCons{zz, L1.g.val(Laws.g.bare(a4))}}, L1.g.val(Laws.g.bare(a2)),
        L1.g.val(a2), val_bare(a2)), Equal.cong(V.Json, V.Json, zz => V.JArr{V.JCons{L1.g.val(a2), zz}},
        L1.g.val(Laws.g.bare(a4)), L1.g.val(a4), val_bare(a4)))
    case D3.GObj0{_a1}:
      {==}
    case D3.GObj{_a1, +a2, _a3, _a4, +a5, _a6, +a7}:
      Equal.trans(V.Json, V.JObj{V.JPair{D3.spelled(a2), L1.g.val(Laws.g.bare(a5)), L1.g.val(Laws.g.bare(a7))}},
        V.JObj{V.JPair{D3.spelled(a2), L1.g.val(a5), L1.g.val(Laws.g.bare(a7))}},
        V.JObj{V.JPair{D3.spelled(a2), L1.g.val(a5), L1.g.val(a7)}}, Equal.cong(V.Json, V.Json,
        zz => V.JObj{V.JPair{D3.spelled(a2), zz, L1.g.val(Laws.g.bare(a7))}}, L1.g.val(Laws.g.bare(a5)),
        L1.g.val(a5), val_bare(a5)), Equal.cong(V.Json, V.Json, zz => V.JObj{V.JPair{D3.spelled(a2),
        L1.g.val(a5), zz}}, L1.g.val(Laws.g.bare(a7)), L1.g.val(a7), val_bare(a7)))
    case D3.GEnd{}:
      {==}
    case D3.GNext{_a1, +a2, _a3, +a4}:
      Equal.trans(V.Json, V.JCons{L1.g.val(Laws.g.bare(a2)), L1.g.val(Laws.g.bare(a4))}, V.JCons{L1.g.val(a2),
        L1.g.val(Laws.g.bare(a4))}, V.JCons{L1.g.val(a2), L1.g.val(a4)}, Equal.cong(V.Json, V.Json,
        zz => V.JCons{zz, L1.g.val(Laws.g.bare(a4))}, L1.g.val(Laws.g.bare(a2)), L1.g.val(a2), val_bare(a2)),
        Equal.cong(V.Json, V.Json, zz => V.JCons{L1.g.val(a2), zz}, L1.g.val(Laws.g.bare(a4)), L1.g.val(a4),
        val_bare(a4)))
    case D3.GNextM{_a1, +a2, _a3, _a4, +a5, _a6, +a7}:
      Equal.trans(V.Json, V.JPair{D3.spelled(a2), L1.g.val(Laws.g.bare(a5)), L1.g.val(Laws.g.bare(a7))},
        V.JPair{D3.spelled(a2), L1.g.val(a5), L1.g.val(Laws.g.bare(a7))}, V.JPair{D3.spelled(a2),
        L1.g.val(a5), L1.g.val(a7)}, Equal.cong(V.Json, V.Json, zz => V.JPair{D3.spelled(a2), zz,
        L1.g.val(Laws.g.bare(a7))}, L1.g.val(Laws.g.bare(a5)), L1.g.val(a5), val_bare(a5)), Equal.cong(V.Json,
        V.Json, zz => V.JPair{D3.spelled(a2), L1.g.val(a5), zz}, L1.g.val(Laws.g.bare(a7)), L1.g.val(a7),
        val_bare(a7)))

def Laws.ws_same(gg, hh, wa, wb, wc, wd, h_g, h_h, h_e, h_sg, h_sh):
  Equal.trans(Maybe<&2, V.Json>, D1.own_m(Ezjson.parse(wc ++ D3.g.text(hh) ++ wd)), Some{L1.g.val(hh)},
    D1.own_m(Ezjson.parse(wa ++ D3.g.text(gg) ++ wb)), L1.text_some(hh, wc, wd, M6.and_left(D3.g.ok(hh,
    D3.GKVal{}), D1.all_ws(wd), M6.and_right(D1.all_ws(wc), Bool.and(D3.g.ok(hh, D3.GKVal{}), D1.all_ws(wd)),
    h_h)), M6.and_left(D1.all_ws(wc), Bool.and(D3.g.ok(hh, D3.GKVal{}), D1.all_ws(wd)), h_h),
    M6.and_right(D3.g.ok(hh, D3.GKVal{}), D1.all_ws(wd), M6.and_right(D1.all_ws(wc), Bool.and(D3.g.ok(hh,
    D3.GKVal{}), D1.all_ws(wd)), h_h)), h_sh), Equal.trans(Maybe<&2, V.Json>, Some{L1.g.val(hh)},
    Some{L1.g.val(Laws.g.bare(hh))}, D1.own_m(Ezjson.parse(wa ++ D3.g.text(gg) ++ wb)), Equal.cong(V.Json,
    Maybe<&2, V.Json>, zz => Some{zz}, L1.g.val(hh), L1.g.val(Laws.g.bare(hh)), Equal.sym(V.Json,
    L1.g.val(Laws.g.bare(hh)), L1.g.val(hh), val_bare(hh))), Equal.trans(Maybe<&2, V.Json>,
    Some{L1.g.val(Laws.g.bare(hh))}, Some{L1.g.val(Laws.g.bare(gg))},
    D1.own_m(Ezjson.parse(wa ++ D3.g.text(gg) ++ wb)), Equal.cong(D3.Gv, Maybe<&2, V.Json>,
    zz => Some{L1.g.val(zz)}, Laws.g.bare(hh), Laws.g.bare(gg), Equal.sym(D3.Gv, Laws.g.bare(gg), Laws.g.bare(hh),
    h_e)), Equal.trans(Maybe<&2, V.Json>, Some{L1.g.val(Laws.g.bare(gg))}, Some{L1.g.val(gg)},
    D1.own_m(Ezjson.parse(wa ++ D3.g.text(gg) ++ wb)), Equal.cong(V.Json, Maybe<&2, V.Json>, zz => Some{zz},
    L1.g.val(Laws.g.bare(gg)), L1.g.val(gg), val_bare(gg)), Equal.sym(Maybe<&2, V.Json>,
    D1.own_m(Ezjson.parse(wa ++ D3.g.text(gg) ++ wb)), Some{L1.g.val(gg)}, L1.text_some(gg, wa, wb,
    M6.and_left(D3.g.ok(gg, D3.GKVal{}), D1.all_ws(wb), M6.and_right(D1.all_ws(wa), Bool.and(D3.g.ok(gg,
    D3.GKVal{}), D1.all_ws(wb)), h_g)), M6.and_left(D1.all_ws(wa), Bool.and(D3.g.ok(gg, D3.GKVal{}),
    D1.all_ws(wb)), h_g), M6.and_right(D3.g.ok(gg, D3.GKVal{}), D1.all_ws(wb), M6.and_right(D1.all_ws(wa),
    Bool.and(D3.g.ok(gg, D3.GKVal{}), D1.all_ws(wb)), h_g)), h_sg))))))

# past a fault the scan stays there
law sc_bad:
  for +txt: String
  {M3.sc.run(txt, M3.SBad{}) == M3.SBad{} : M3.Sc}

def sc_bad(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{_hd, +tl}:
      sc_bad(tl)

# a text that is whitespace, a derivation and whitespace passes the scan
law acc_der:
  for +wa: String
  for +gg: D3.Gv
  for +wb: String
  for +h_d: {D3.derived(wa, gg, wb) == True{} : Bool}
  {M3.sc.acc(M3.sc.run(wa ++ D3.g.text(gg) ++ wb, M3.SOut{M3.LSt{}, 0n})) == True{} : Bool}

def acc_der(wa, gg, wb, h_d):
  Equal.cong(M3.Sc, Bool, zz => M3.sc.top(zz), M3.sc.fin(M3.sc.run(wa ++ D3.g.text(gg) ++ wb, M3.SOut{M3.LSt{}, 0n})),
      M3.SOut{M3.LVal{},
    0n}, M3.tr(wa, D3.g.text(gg) ++ wb, M3.SOut{M3.LSt{}, 0n}, M3.SOut{M3.LSt{}, 0n}, M3.SOut{M3.LVal{}, 0n},
        M3.p_ws(wa,
    M6.and_left(D1.all_ws(wa), Bool.and(D3.g.ok(gg, D3.GKVal{}), D1.all_ws(wb)), h_d), M3.LSt{}, 0n, M3.SOut{M3.LSt{},
        0n},
    {==}), +y0 => e0 => M3.tr(D3.g.text(gg), wb, y0, M3.SOut{M3.LVal{}, 0n}, M3.SOut{M3.LVal{}, 0n}, M3.g1(gg,
        D3.GKVal{},
    M6.and_left(D3.g.ok(gg, D3.GKVal{}), D1.all_ws(wb), M6.and_right(D1.all_ws(wa), Bool.and(D3.g.ok(gg,
    D3.GKVal{}), D1.all_ws(wb)), h_d)), M3.LSt{}, 0n, {==}, y0, e0), +y1 => e1 => M3.p_ws(wb, M6.and_right(D3.g.ok(gg,
    D3.GKVal{}), D1.all_ws(wb), M6.and_right(D1.all_ws(wa), Bool.and(D3.g.ok(gg, D3.GKVal{}), D1.all_ws(wb)),
    h_d)), M3.LVal{}, 0n, y1, e1))))

# when both ways are false
law when_ff:
  for bv: Bool
  {D1.when(bv, False{}, False{}) == False{} : Bool}

def when_ff(bv):
  match bv:
    case True{}:
      {==}
    case False{}:
      {==}

# RFC 8259 §6, digits_end: a text that ends in a character that is no digit fails
law nf_digits_end:
  for +xs: List<&2, Char>
  for +cc: Char
  for +hd: {D2.digit(cc) == False{} : Bool}
  for +h45: {D1.is_cp(cc, 45) == False{} : Bool}
  for +h48: {D1.is_cp(cc, 48) == False{} : Bool}
  for +h19: {D1.digit19(cc) == False{} : Bool}
  {D1.digits_end(List.append(&2, Char, xs, [cc])) == False{} : Bool}

def nf_digits_end(xs, cc, hd, h45, h48, h19):
  match xs:
    case Nil{}:
      Equal.cong(Bool, Bool, zz => D1.when(zz, True{}, False{}), D2.digit(cc), False{}, hd)
    case +x <> +tl:
      Equal.trans(Bool, D1.when(D2.digit(x), D1.digits_end(List.append(&2, Char, tl, [cc])), False{}),
        D1.when(D2.digit(x), False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D2.digit(x), zz,
        False{}), D1.digits_end(List.append(&2, Char, tl, [cc])), False{}, nf_digits_end(tl, cc, hd, h45, h48, h19)),
        when_ff(D2.digit(x)))

# RFC 8259 §6, digits1_end: a text that ends in a character that is no digit fails
law nf_digits1_end:
  for +xs: List<&2, Char>
  for +cc: Char
  for +hd: {D2.digit(cc) == False{} : Bool}
  for +h45: {D1.is_cp(cc, 45) == False{} : Bool}
  for +h48: {D1.is_cp(cc, 48) == False{} : Bool}
  for +h19: {D1.digit19(cc) == False{} : Bool}
  {D1.digits1_end(List.append(&2, Char, xs, [cc])) == False{} : Bool}

def nf_digits1_end(xs, cc, hd, h45, h48, h19):
  match xs:
    case Nil{}:
      Equal.cong(Bool, Bool, zz => D1.when(zz, True{}, False{}), D2.digit(cc), False{}, hd)
    case +x <> +tl:
      Equal.trans(Bool, D1.when(D2.digit(x), D1.digits_end(List.append(&2, Char, tl, [cc])), False{}),
        D1.when(D2.digit(x), False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D2.digit(x), zz,
        False{}), D1.digits_end(List.append(&2, Char, tl, [cc])), False{}, nf_digits_end(tl, cc, hd, h45, h48, h19)),
        when_ff(D2.digit(x)))

# RFC 8259 §6, exp_body: a text that ends in a character that is no digit fails
law nf_exp_body:
  for +xs: List<&2, Char>
  for +cc: Char
  for +hd: {D2.digit(cc) == False{} : Bool}
  for +h45: {D1.is_cp(cc, 45) == False{} : Bool}
  for +h48: {D1.is_cp(cc, 48) == False{} : Bool}
  for +h19: {D1.digit19(cc) == False{} : Bool}
  {D1.exp_body(List.append(&2, Char, xs, [cc])) == False{} : Bool}

def nf_exp_body(xs, cc, hd, h45, h48, h19):
  match xs:
    case Nil{}:
      Equal.trans(Bool, D1.when(D1.is_cp(cc, 43), False{}, D1.when(D1.is_cp(cc, 45), False{},
        D1.when(D2.digit(cc), True{}, False{}))), D1.when(D1.is_cp(cc, 43), False{}, False{}), False{},
        Equal.cong(Bool, Bool, zz => D1.when(D1.is_cp(cc, 43), False{}, zz), D1.when(D1.is_cp(cc, 45), False{},
        D1.when(D2.digit(cc), True{}, False{})), False{}, Equal.trans(Bool, D1.when(D1.is_cp(cc, 45), False{},
        D1.when(D2.digit(cc), True{}, False{})), D1.when(False{}, False{}, D1.when(D2.digit(cc), True{},
        False{})), False{}, Equal.cong(Bool, Bool, zz => D1.when(zz, False{}, D1.when(D2.digit(cc), True{},
        False{})), D1.is_cp(cc, 45), False{}, h45), Equal.cong(Bool, Bool, zz => D1.when(zz, True{}, False{}),
        D2.digit(cc), False{}, hd))), when_ff(D1.is_cp(cc, 43)))
    case +x <> +tl:
      Equal.trans(Bool, D1.when(D1.is_cp(x, 43), D1.digits1_end(List.append(&2, Char, tl, [cc])),
        D1.when(D1.is_cp(x, 45), D1.digits1_end(List.append(&2, Char, tl, [cc])), D1.when(D2.digit(x),
        D1.digits_end(List.append(&2, Char, tl, [cc])), False{}))), D1.when(D1.is_cp(x, 43), False{},
        D1.when(D1.is_cp(x, 45), D1.digits1_end(List.append(&2, Char, tl, [cc])), D1.when(D2.digit(x),
        D1.digits_end(List.append(&2, Char, tl, [cc])), False{}))), False{}, Equal.cong(Bool, Bool,
        zz => D1.when(D1.is_cp(x, 43), zz, D1.when(D1.is_cp(x, 45), D1.digits1_end(List.append(&2, Char, tl,
        [cc])), D1.when(D2.digit(x), D1.digits_end(List.append(&2, Char, tl, [cc])), False{}))),
        D1.digits1_end(List.append(&2, Char, tl, [cc])), False{}, nf_digits1_end(tl, cc, hd, h45, h48, h19)),
        Equal.trans(Bool, D1.when(D1.is_cp(x, 43), False{}, D1.when(D1.is_cp(x, 45),
        D1.digits1_end(List.append(&2, Char, tl, [cc])), D1.when(D2.digit(x), D1.digits_end(List.append(&2,
        Char, tl, [cc])), False{}))), D1.when(D1.is_cp(x, 43), False{}, False{}), False{}, Equal.cong(Bool, Bool,
        zz => D1.when(D1.is_cp(x, 43), False{}, zz), D1.when(D1.is_cp(x, 45), D1.digits1_end(List.append(&2,
        Char, tl, [cc])), D1.when(D2.digit(x), D1.digits_end(List.append(&2, Char, tl, [cc])), False{})),
        False{}, Equal.trans(Bool, D1.when(D1.is_cp(x, 45), D1.digits1_end(List.append(&2, Char, tl, [cc])),
        D1.when(D2.digit(x), D1.digits_end(List.append(&2, Char, tl, [cc])), False{})), D1.when(D1.is_cp(x,
        45), False{}, D1.when(D2.digit(x), D1.digits_end(List.append(&2, Char, tl, [cc])), False{})), False{},
        Equal.cong(Bool, Bool, zz => D1.when(D1.is_cp(x, 45), zz, D1.when(D2.digit(x),
        D1.digits_end(List.append(&2, Char, tl, [cc])), False{})), D1.digits1_end(List.append(&2, Char, tl, [cc])),
        False{}, nf_digits1_end(tl, cc, hd, h45, h48, h19)), Equal.trans(Bool, D1.when(D1.is_cp(x, 45), False{},
        D1.when(D2.digit(x), D1.digits_end(List.append(&2, Char, tl, [cc])), False{})), D1.when(D1.is_cp(x,
        45), False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D1.is_cp(x, 45), False{}, zz),
        D1.when(D2.digit(x), D1.digits_end(List.append(&2, Char, tl, [cc])), False{}), False{}, Equal.trans(Bool,
        D1.when(D2.digit(x), D1.digits_end(List.append(&2, Char, tl, [cc])), False{}), D1.when(D2.digit(x),
        False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D2.digit(x), zz, False{}),
        D1.digits_end(List.append(&2, Char, tl, [cc])), False{}, nf_digits_end(tl, cc, hd, h45, h48, h19)),
        when_ff(D2.digit(x)))), when_ff(D1.is_cp(x, 45))))), when_ff(D1.is_cp(x, 43))))

# RFC 8259 §6, digits_exp_end: a text that ends in a character that is no digit fails
law nf_digits_exp_end:
  for +xs: List<&2, Char>
  for +cc: Char
  for +hd: {D2.digit(cc) == False{} : Bool}
  for +h45: {D1.is_cp(cc, 45) == False{} : Bool}
  for +h48: {D1.is_cp(cc, 48) == False{} : Bool}
  for +h19: {D1.digit19(cc) == False{} : Bool}
  {D1.digits_exp_end(List.append(&2, Char, xs, [cc])) == False{} : Bool}

def nf_digits_exp_end(xs, cc, hd, h45, h48, h19):
  match xs:
    case Nil{}:
      Equal.trans(Bool, D1.when(D2.digit(cc), True{}, D1.when(D1.is_e(cc), False{}, False{})),
        D1.when(False{}, True{}, D1.when(D1.is_e(cc), False{}, False{})), False{}, Equal.cong(Bool, Bool,
        zz => D1.when(zz, True{}, D1.when(D1.is_e(cc), False{}, False{})), D2.digit(cc), False{}, hd),
        when_ff(D1.is_e(cc)))
    case +x <> +tl:
      Equal.trans(Bool, D1.when(D2.digit(x), D1.digits_exp_end(List.append(&2, Char, tl, [cc])),
        D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{})), D1.when(D2.digit(x),
        False{}, D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{})), False{},
        Equal.cong(Bool, Bool, zz => D1.when(D2.digit(x), zz, D1.when(D1.is_e(x), D1.exp_body(List.append(&2,
        Char, tl, [cc])), False{})), D1.digits_exp_end(List.append(&2, Char, tl, [cc])), False{},
        nf_digits_exp_end(tl, cc, hd, h45, h48, h19)), Equal.trans(Bool, D1.when(D2.digit(x), False{},
        D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{})), D1.when(D2.digit(x),
        False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D2.digit(x), False{}, zz),
        D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{}), False{}, Equal.trans(Bool,
        D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{}), D1.when(D1.is_e(x),
        False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D1.is_e(x), zz, False{}),
        D1.exp_body(List.append(&2, Char, tl, [cc])), False{}, nf_exp_body(tl, cc, hd, h45, h48, h19)),
        when_ff(D1.is_e(x)))), when_ff(D2.digit(x))))

# RFC 8259 §6, frac_body: a text that ends in a character that is no digit fails
law nf_frac_body:
  for +xs: List<&2, Char>
  for +cc: Char
  for +hd: {D2.digit(cc) == False{} : Bool}
  for +h45: {D1.is_cp(cc, 45) == False{} : Bool}
  for +h48: {D1.is_cp(cc, 48) == False{} : Bool}
  for +h19: {D1.digit19(cc) == False{} : Bool}
  {D1.frac_body(List.append(&2, Char, xs, [cc])) == False{} : Bool}

def nf_frac_body(xs, cc, hd, h45, h48, h19):
  match xs:
    case Nil{}:
      Equal.cong(Bool, Bool, zz => D1.when(zz, True{}, False{}), D2.digit(cc), False{}, hd)
    case +x <> +tl:
      Equal.trans(Bool, D1.when(D2.digit(x), D1.digits_exp_end(List.append(&2, Char, tl, [cc])), False{}),
        D1.when(D2.digit(x), False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D2.digit(x), zz,
        False{}), D1.digits_exp_end(List.append(&2, Char, tl, [cc])), False{}, nf_digits_exp_end(tl, cc, hd, h45,
        h48, h19)), when_ff(D2.digit(x)))

# RFC 8259 §6, zero_rest: a text that ends in a character that is no digit fails
law nf_zero_rest:
  for +xs: List<&2, Char>
  for +cc: Char
  for +hd: {D2.digit(cc) == False{} : Bool}
  for +h45: {D1.is_cp(cc, 45) == False{} : Bool}
  for +h48: {D1.is_cp(cc, 48) == False{} : Bool}
  for +h19: {D1.digit19(cc) == False{} : Bool}
  {D1.zero_rest(List.append(&2, Char, xs, [cc])) == False{} : Bool}

def nf_zero_rest(xs, cc, hd, h45, h48, h19):
  match xs:
    case Nil{}:
      Equal.trans(Bool, D1.when(D2.digit(cc), False{}, D1.when(D1.is_cp(cc, 46), False{},
        D1.when(D1.is_e(cc), False{}, False{}))), D1.when(False{}, False{}, D1.when(D1.is_cp(cc, 46),
        False{}, D1.when(D1.is_e(cc), False{}, False{}))), False{}, Equal.cong(Bool, Bool, zz => D1.when(zz,
        False{}, D1.when(D1.is_cp(cc, 46), False{}, D1.when(D1.is_e(cc), False{}, False{}))), D2.digit(cc),
        False{}, hd), Equal.trans(Bool, D1.when(D1.is_cp(cc, 46), False{}, D1.when(D1.is_e(cc), False{},
        False{})), D1.when(D1.is_cp(cc, 46), False{}, False{}), False{}, Equal.cong(Bool, Bool,
        zz => D1.when(D1.is_cp(cc, 46), False{}, zz), D1.when(D1.is_e(cc), False{}, False{}), False{},
        when_ff(D1.is_e(cc))), when_ff(D1.is_cp(cc, 46))))
    case +x <> +tl:
      Equal.trans(Bool, D1.when(D2.digit(x), False{}, D1.when(D1.is_cp(x, 46), D1.frac_body(List.append(&2,
        Char, tl, [cc])), D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{}))),
        D1.when(D2.digit(x), False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D2.digit(x),
        False{}, zz), D1.when(D1.is_cp(x, 46), D1.frac_body(List.append(&2, Char, tl, [cc])),
        D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{})), False{}, Equal.trans(Bool,
        D1.when(D1.is_cp(x, 46), D1.frac_body(List.append(&2, Char, tl, [cc])), D1.when(D1.is_e(x),
        D1.exp_body(List.append(&2, Char, tl, [cc])), False{})), D1.when(D1.is_cp(x, 46), False{},
        D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{})), False{}, Equal.cong(Bool,
        Bool, zz => D1.when(D1.is_cp(x, 46), zz, D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl,
        [cc])), False{})), D1.frac_body(List.append(&2, Char, tl, [cc])), False{}, nf_frac_body(tl, cc, hd, h45, h48,
        h19)), Equal.trans(Bool, D1.when(D1.is_cp(x, 46), False{}, D1.when(D1.is_e(x),
        D1.exp_body(List.append(&2, Char, tl, [cc])), False{})), D1.when(D1.is_cp(x, 46), False{}, False{}),
        False{}, Equal.cong(Bool, Bool, zz => D1.when(D1.is_cp(x, 46), False{}, zz), D1.when(D1.is_e(x),
        D1.exp_body(List.append(&2, Char, tl, [cc])), False{}), False{}, Equal.trans(Bool, D1.when(D1.is_e(x),
        D1.exp_body(List.append(&2, Char, tl, [cc])), False{}), D1.when(D1.is_e(x), False{}, False{}), False{},
        Equal.cong(Bool, Bool, zz => D1.when(D1.is_e(x), zz, False{}), D1.exp_body(List.append(&2, Char, tl,
        [cc])), False{}, nf_exp_body(tl, cc, hd, h45, h48, h19)), when_ff(D1.is_e(x)))), when_ff(D1.is_cp(x,
        46))))), when_ff(D2.digit(x)))

# RFC 8259 §6, digits_rest: a text that ends in a character that is no digit fails
law nf_digits_rest:
  for +xs: List<&2, Char>
  for +cc: Char
  for +hd: {D2.digit(cc) == False{} : Bool}
  for +h45: {D1.is_cp(cc, 45) == False{} : Bool}
  for +h48: {D1.is_cp(cc, 48) == False{} : Bool}
  for +h19: {D1.digit19(cc) == False{} : Bool}
  {D1.digits_rest(List.append(&2, Char, xs, [cc])) == False{} : Bool}

def nf_digits_rest(xs, cc, hd, h45, h48, h19):
  match xs:
    case Nil{}:
      Equal.trans(Bool, D1.when(D2.digit(cc), True{}, D1.when(D1.is_cp(cc, 46), False{},
        D1.when(D1.is_e(cc), False{}, False{}))), D1.when(False{}, True{}, D1.when(D1.is_cp(cc, 46), False{},
        D1.when(D1.is_e(cc), False{}, False{}))), False{}, Equal.cong(Bool, Bool, zz => D1.when(zz, True{},
        D1.when(D1.is_cp(cc, 46), False{}, D1.when(D1.is_e(cc), False{}, False{}))), D2.digit(cc), False{},
        hd), Equal.trans(Bool, D1.when(D1.is_cp(cc, 46), False{}, D1.when(D1.is_e(cc), False{}, False{})),
        D1.when(D1.is_cp(cc, 46), False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D1.is_cp(cc,
        46), False{}, zz), D1.when(D1.is_e(cc), False{}, False{}), False{}, when_ff(D1.is_e(cc))),
        when_ff(D1.is_cp(cc, 46))))
    case +x <> +tl:
      Equal.trans(Bool, D1.when(D2.digit(x), D1.digits_rest(List.append(&2, Char, tl, [cc])),
        D1.when(D1.is_cp(x, 46), D1.frac_body(List.append(&2, Char, tl, [cc])), D1.when(D1.is_e(x),
        D1.exp_body(List.append(&2, Char, tl, [cc])), False{}))), D1.when(D2.digit(x), False{},
        D1.when(D1.is_cp(x, 46), D1.frac_body(List.append(&2, Char, tl, [cc])), D1.when(D1.is_e(x),
        D1.exp_body(List.append(&2, Char, tl, [cc])), False{}))), False{}, Equal.cong(Bool, Bool,
        zz => D1.when(D2.digit(x), zz, D1.when(D1.is_cp(x, 46), D1.frac_body(List.append(&2, Char, tl,
        [cc])), D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{}))),
        D1.digits_rest(List.append(&2, Char, tl, [cc])), False{}, nf_digits_rest(tl, cc, hd, h45, h48, h19)),
        Equal.trans(Bool, D1.when(D2.digit(x), False{}, D1.when(D1.is_cp(x, 46), D1.frac_body(List.append(&2,
        Char, tl, [cc])), D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{}))),
        D1.when(D2.digit(x), False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D2.digit(x),
        False{}, zz), D1.when(D1.is_cp(x, 46), D1.frac_body(List.append(&2, Char, tl, [cc])),
        D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{})), False{}, Equal.trans(Bool,
        D1.when(D1.is_cp(x, 46), D1.frac_body(List.append(&2, Char, tl, [cc])), D1.when(D1.is_e(x),
        D1.exp_body(List.append(&2, Char, tl, [cc])), False{})), D1.when(D1.is_cp(x, 46), False{},
        D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl, [cc])), False{})), False{}, Equal.cong(Bool,
        Bool, zz => D1.when(D1.is_cp(x, 46), zz, D1.when(D1.is_e(x), D1.exp_body(List.append(&2, Char, tl,
        [cc])), False{})), D1.frac_body(List.append(&2, Char, tl, [cc])), False{}, nf_frac_body(tl, cc, hd, h45, h48,
        h19)), Equal.trans(Bool, D1.when(D1.is_cp(x, 46), False{}, D1.when(D1.is_e(x),
        D1.exp_body(List.append(&2, Char, tl, [cc])), False{})), D1.when(D1.is_cp(x, 46), False{}, False{}),
        False{}, Equal.cong(Bool, Bool, zz => D1.when(D1.is_cp(x, 46), False{}, zz), D1.when(D1.is_e(x),
        D1.exp_body(List.append(&2, Char, tl, [cc])), False{}), False{}, Equal.trans(Bool, D1.when(D1.is_e(x),
        D1.exp_body(List.append(&2, Char, tl, [cc])), False{}), D1.when(D1.is_e(x), False{}, False{}), False{},
        Equal.cong(Bool, Bool, zz => D1.when(D1.is_e(x), zz, False{}), D1.exp_body(List.append(&2, Char, tl,
        [cc])), False{}, nf_exp_body(tl, cc, hd, h45, h48, h19)), when_ff(D1.is_e(x)))), when_ff(D1.is_cp(x,
        46))))), when_ff(D2.digit(x))))

# RFC 8259 §6, int_end: a text that ends in a character that is no digit fails
law nf_int_end:
  for +xs: List<&2, Char>
  for +cc: Char
  for +hd: {D2.digit(cc) == False{} : Bool}
  for +h45: {D1.is_cp(cc, 45) == False{} : Bool}
  for +h48: {D1.is_cp(cc, 48) == False{} : Bool}
  for +h19: {D1.digit19(cc) == False{} : Bool}
  {D1.int_end(List.append(&2, Char, xs, [cc])) == False{} : Bool}

def nf_int_end(xs, cc, hd, h45, h48, h19):
  match xs:
    case Nil{}:
      Equal.trans(Bool, D1.when(D1.is_cp(cc, 48), True{}, D1.when(D1.digit19(cc), True{}, False{})),
        D1.when(False{}, True{}, D1.when(D1.digit19(cc), True{}, False{})), False{}, Equal.cong(Bool, Bool,
        zz => D1.when(zz, True{}, D1.when(D1.digit19(cc), True{}, False{})), D1.is_cp(cc, 48), False{}, h48),
        Equal.cong(Bool, Bool, zz => D1.when(zz, True{}, False{}), D1.digit19(cc), False{}, h19))
    case +x <> +tl:
      Equal.trans(Bool, D1.when(D1.is_cp(x, 48), D1.zero_rest(List.append(&2, Char, tl, [cc])),
        D1.when(D1.digit19(x), D1.digits_rest(List.append(&2, Char, tl, [cc])), False{})),
        D1.when(D1.is_cp(x, 48), False{}, D1.when(D1.digit19(x), D1.digits_rest(List.append(&2, Char, tl,
        [cc])), False{})), False{}, Equal.cong(Bool, Bool, zz => D1.when(D1.is_cp(x, 48), zz,
        D1.when(D1.digit19(x), D1.digits_rest(List.append(&2, Char, tl, [cc])), False{})),
        D1.zero_rest(List.append(&2, Char, tl, [cc])), False{}, nf_zero_rest(tl, cc, hd, h45, h48, h19)),
        Equal.trans(Bool, D1.when(D1.is_cp(x, 48), False{}, D1.when(D1.digit19(x),
        D1.digits_rest(List.append(&2, Char, tl, [cc])), False{})), D1.when(D1.is_cp(x, 48), False{}, False{}),
        False{}, Equal.cong(Bool, Bool, zz => D1.when(D1.is_cp(x, 48), False{}, zz), D1.when(D1.digit19(x),
        D1.digits_rest(List.append(&2, Char, tl, [cc])), False{}), False{}, Equal.trans(Bool,
        D1.when(D1.digit19(x), D1.digits_rest(List.append(&2, Char, tl, [cc])), False{}),
        D1.when(D1.digit19(x), False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D1.digit19(x),
        zz, False{}), D1.digits_rest(List.append(&2, Char, tl, [cc])), False{}, nf_digits_rest(tl, cc, hd, h45, h48,
        h19)), when_ff(D1.digit19(x)))), when_ff(D1.is_cp(x, 48))))

# RFC 8259 §6, number: a text that ends in a character that is no digit fails
law nf_number:
  for +xs: List<&2, Char>
  for +cc: Char
  for +hd: {D2.digit(cc) == False{} : Bool}
  for +h45: {D1.is_cp(cc, 45) == False{} : Bool}
  for +h48: {D1.is_cp(cc, 48) == False{} : Bool}
  for +h19: {D1.digit19(cc) == False{} : Bool}
  {D1.number(List.append(&2, Char, xs, [cc])) == False{} : Bool}

def nf_number(xs, cc, hd, h45, h48, h19):
  match xs:
    case Nil{}:
      Equal.trans(Bool, D1.when(D1.is_cp(cc, 45), False{}, D1.int_end([cc])), D1.when(False{}, False{},
        D1.int_end([cc])), False{}, Equal.cong(Bool, Bool, zz => D1.when(zz, False{}, D1.int_end([cc])),
        D1.is_cp(cc, 45), False{}, h45), nf_int_end([], cc, hd, h45, h48, h19))
    case +x <> +tl:
      Equal.trans(Bool, D1.when(D1.is_cp(x, 45), D1.int_end(List.append(&2, Char, tl, [cc])),
        D1.int_end(x <> List.append(&2, Char, tl, [cc]))), D1.when(D1.is_cp(x, 45), False{},
        D1.int_end(x <> List.append(&2, Char, tl, [cc]))), False{}, Equal.cong(Bool, Bool,
        zz => D1.when(D1.is_cp(x, 45), zz, D1.int_end(x <> List.append(&2, Char, tl, [cc]))),
        D1.int_end(List.append(&2, Char, tl, [cc])), False{}, nf_int_end(tl, cc, hd, h45, h48, h19)),
        Equal.trans(Bool, D1.when(D1.is_cp(x, 45), False{}, D1.int_end(x <> List.append(&2, Char, tl, [cc]))),
        D1.when(D1.is_cp(x, 45), False{}, False{}), False{}, Equal.cong(Bool, Bool, zz => D1.when(D1.is_cp(x,
        45), False{}, zz), D1.int_end(x <> List.append(&2, Char, tl, [cc])), False{}, nf_int_end(x <> tl, cc, hd,
        h45, h48, h19)), when_ff(D1.is_cp(x, 45))))

law c19.at:
  for bv: Bool
  for +cc: Char
  for e: {D1.digit19(cc) == bv : Bool}
  for hd: {D2.digit(cc) == False{} : Bool}
  {D1.digit19(cc) == False{} : Bool}

def c19.at(bv, cc, e, hd):
  match bv:
    case False{}:
      e
    case True{}:
      Empty.absurd({D1.digit19(cc) == False{} : Bool}, M1.true_false(Equal.trans(Bool, True{}, D2.digit(cc), False{},
        Equal.sym(Bool, D2.digit(cc), True{}, M9.d19(cc, e)), hd)))

law c19:
  for +cc: Char
  for hd: {D2.digit(cc) == False{} : Bool}
  {D1.digit19(cc) == False{} : Bool}

def c19(cc, hd):
  c19.at(D1.digit19(cc), cc, {==}, hd)

# a number starts with `-` or a digit
law num_first:
  for +cc: Char
  for +xs: List<&2, Char>
  for h45: {D1.is_cp(cc, 45) == False{} : Bool}
  for h48: {D1.is_cp(cc, 48) == False{} : Bool}
  for h19: {D1.digit19(cc) == False{} : Bool}
  {D1.number(cc <> xs) == False{} : Bool}

def num_first(cc, xs, h45, h48, h19):
  s45 = Equal.sym(Bool, D1.is_cp(cc, 45), False{}, h45)
  %s45 : {D1.when(_, D1.int_end(xs), D1.int_end(cc <> xs)) == False{} : Bool}
  s48 = Equal.sym(Bool, D1.is_cp(cc, 48), False{}, h48)
  %s48 : {D1.when(_, D1.zero_rest(xs), D1.when(D1.digit19(cc), D1.digits_rest(xs),
    False{})) == False{} : Bool}
  s19 = Equal.sym(Bool, D1.digit19(cc), False{}, h19)
  %s19 : {D1.when(_, D1.digits_rest(xs), False{}) == False{} : Bool}
  {==}

# two strings that differ compare unequal
law eq_f.at:
  for bv: Bool
  for +aa: String
  for +bb: String
  for e: {String.eq(aa, bb) == bv : Bool}
  for kk: {aa == bb : String} -> Empty
  {String.eq(aa, bb) == False{} : Bool}

def eq_f.at(bv, aa, bb, e, kk):
  match bv:
    case False{}:
      e
    case True{}:
      Empty.absurd({String.eq(aa, bb) == False{} : Bool}, kk(M8.str_eq_sound(aa, bb, e)))

law eq_f:
  for +aa: String
  for +bb: String
  for kk: {aa == bb : String} -> Empty
  {String.eq(aa, bb) == False{} : Bool}

def eq_f(aa, bb, kk):
  eq_f.at(String.eq(aa, bb), aa, bb, {==}, kk)

# four alternatives, each false
law or4f:
  for aa: Bool
  for bb: Bool
  for cc: Bool
  for dd: Bool
  for ha: {aa == False{} : Bool}
  for hb: {bb == False{} : Bool}
  for hc: {cc == False{} : Bool}
  for hd: {dd == False{} : Bool}
  {Bool.or(aa, Bool.or(bb, Bool.or(cc, dd))) == False{} : Bool}

def or4f(aa, bb, cc, dd, ha, hb, hc, hd):
  sa = Equal.sym(Bool, aa, False{}, ha)
  %sa : {Bool.or(_, Bool.or(bb, Bool.or(cc, dd))) == False{} : Bool}
  sb = Equal.sym(Bool, bb, False{}, hb)
  %sb : {Bool.or(_, Bool.or(cc, dd)) == False{} : Bool}
  sc = Equal.sym(Bool, cc, False{}, hc)
  %sc : {Bool.or(_, dd) == False{} : Bool}
  hd

# the first character and the rest of a string
def s_hd(txt: String) -> Char:
  match txt:
    case SNil{}:
      Char.from_u32(0)
    case SCon{hd, _}:
      hd

def s_tl(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{_, tl}:
      tl

# a character that is no digit or `-` put in front of a text that is no
# rest of a literal name is no literal name or number
law lon_front:
  for +cc: Char
  for +w: String
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for k1: {w == "ull" : String} -> Empty
  for k2: {w == "rue" : String} -> Empty
  for k3: {w == "alse" : String} -> Empty
  {D1.lit_or_num(SCon{cc, w}) == False{} : Bool}

def lon_front(cc, w, hn, k1, k2, k3):
  +hd = M10.or_false_l(D2.digit(cc), D1.is_cp(cc, 45), hn)
  or4f(String.eq(SCon{cc, w}, "null"), String.eq(SCon{cc, w}, "true"), String.eq(SCon{cc, w}, "false"),
    D1.number(cc <> String.to_list(w)),
    eq_f(SCon{cc, w}, "null", ee => k1(Equal.cong(String, String, zz => s_tl(zz), SCon{cc, w}, "null", ee))),
    eq_f(SCon{cc, w}, "true", ee => k2(Equal.cong(String, String, zz => s_tl(zz), SCon{cc, w}, "true", ee))),
    eq_f(SCon{cc, w}, "false", ee => k3(Equal.cong(String, String, zz => s_tl(zz), SCon{cc, w}, "false", ee))),
    num_first(cc, String.to_list(w), M10.or_false_r(D2.digit(cc), D1.is_cp(cc, 45), hn), M9.c48(cc, hd), c19(cc, hd)))

# a string that is empty is not one that is not
def s_nil(txt: String) -> Bool:
  match txt:
    case SNil{}:
      True{}
    case SCon{_, _}:
      False{}

law nil_ne:
  for +bb: String
  for hb: {s_nil(bb) == False{} : Bool}
  for ee: {"" == bb : String}
  Empty

def nil_ne(bb, hb, ee):
  M1.true_false(Equal.trans(Bool, True{}, s_nil(bb), False{}, Equal.cong(String, Bool, zz => s_nil(zz), "", bb, ee),
      hb))

# one character, no digit or `-`, is no literal name or number
law lon1:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  {D1.lit_or_num(Lex.text([cc])) == False{} : Bool}

def lon1(cc, hn):
  lon_front(cc, "", hn, ee => nil_ne("ull", {==}, ee), ee => nil_ne("rue", {==}, ee), ee => nil_ne("alse", {==}, ee))

# a literal name or a number with a character that is no digit or `-` in
# front is neither
law lon_cons:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +w: String
  for +h: {D1.lit_or_num(w) == True{} : Bool}
  {D1.lit_or_num(SCon{cc, w}) == False{} : Bool}

def lon_cons(cc, hn, w, h):
  lon_front(cc, w, hn,
    ee => M1.true_false(Equal.trans(Bool, True{}, D1.lit_or_num(w), False{}, Equal.sym(Bool, D1.lit_or_num(w), True{},
      h),
      Equal.cong(String, Bool, zz => D1.lit_or_num(zz), w, "ull", ee))),
    ee => M1.true_false(Equal.trans(Bool, True{}, D1.lit_or_num(w), False{}, Equal.sym(Bool, D1.lit_or_num(w), True{},
      h),
      Equal.cong(String, Bool, zz => D1.lit_or_num(zz), w, "rue", ee))),
    ee => M1.true_false(Equal.trans(Bool, True{}, D1.lit_or_num(w), False{}, Equal.sym(Bool, D1.lit_or_num(w), True{},
      h),
      Equal.cong(String, Bool, zz => D1.lit_or_num(zz), w, "alse", ee))))

# a buffer with one more character read first
law bx_app:
  for +ba: List<&2, Char>
  for +cc: Char
  for +acc: String
  {Lex.text.go(List.append(&2, Char, ba, [cc]), acc) == SCon{cc, Lex.text.go(ba, acc)} : String}

def bx_app(ba, cc, acc):
  match ba:
    case Nil{}:
      {==}
    case +x <> +tl:
      bx_app(tl, cc, SCon{x, acc})

law lon_app:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +ba: List<&2, Char>
  for +h: {D1.lit_or_num(Lex.text(ba)) == True{} : Bool}
  {D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))) == False{} : Bool}

def lon_app(cc, hn, ba, h):
  Equal.trans(Bool, D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))), D1.lit_or_num(SCon{cc, Lex.text(ba)}),
    False{}, Equal.cong(String, Bool, zz => D1.lit_or_num(zz), Lex.text(List.append(&2, Char, ba, [cc])),
    SCon{cc, Lex.text(ba)}, bx_app(ba, cc, "")), lon_cons(cc, hn, Lex.text(ba), h))

# a buffer read onto a text
law tg:
  for +buf: List<&2, Char>
  for +acc: String
  for +bb: String
  {Lex.text.go(buf, acc ++ bb) == Lex.text.go(buf, acc) ++ bb : String}

def tg(buf, acc, bb):
  match buf:
    case Nil{}:
      {==}
    case +x <> +tl:
      tg(tl, SCon{x, acc}, bb)

# a string's characters, one more at the end
law tl_app:
  for +w: String
  for +cc: Char
  {String.to_list(w ++ SCon{cc, ""}) == List.append(&2, Char, String.to_list(w), [cc]) : List<&2, Char>}

def tl_app(w, cc):
  match w:
    case SNil{}:
      {==}
    case SCon{+x, +tl}:
      Equal.cong(List<&2, Char>, List<&2, Char>, zz => x <> zz, String.to_list(tl ++ SCon{cc, ""}),
        List.append(&2, Char, String.to_list(tl), [cc]), tl_app(tl, cc))

# a number's first character, named, is not `n`, `t` or `f`
law num_hd:
  for +x: Char
  for +xs: List<&2, Char>
  for +h: {D1.number(x <> xs) == True{} : Bool}
  for +l0: Char
  for +hl: {D1.number(l0 <> xs) == False{} : Bool}
  for ee: {x == l0 : Char}
  Empty

def num_hd(x, xs, h, l0, hl, ee):
  M1.true_false(Equal.trans(Bool, True{}, D1.number(x <> xs), False{}, Equal.sym(Bool, D1.number(x <> xs), True{}, h),
    Equal.trans(Bool, D1.number(x <> xs), D1.number(l0 <> xs), False{}, Equal.cong(Char, Bool,
    zz => D1.number(zz <> xs), x, l0, ee), hl)))

law lon_snoc.n:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +w: String
  for +h: {D1.number(String.to_list(w)) == True{} : Bool}
  {D1.lit_or_num(w ++ SCon{cc, ""}) == False{} : Bool}

def lon_snoc.n(cc, hn, w, h):
  match w:
    case SNil{}:
      M6.no({D1.lit_or_num("" ++ SCon{cc, ""}) == False{} : Bool}, h)
    case SCon{+x, +t}:
      +aa = SCon{x, t} ++ SCon{cc, ""}
      +xs = String.to_list(t)
      +hd = M10.or_false_l(D2.digit(cc), D1.is_cp(cc, 45), hn)
      or4f(String.eq(aa, "null"), String.eq(aa, "true"), String.eq(aa, "false"), D1.number(String.to_list(aa)),
        eq_f(aa, "null", ee => num_hd(x, xs, h, 'n', {==}, Equal.cong(String, Char, zz => s_hd(zz), aa, "null", ee))),
        eq_f(aa, "true", ee => num_hd(x, xs, h, 't', {==}, Equal.cong(String, Char, zz => s_hd(zz), aa, "true", ee))),
        eq_f(aa, "false", ee => num_hd(x, xs, h, 'f', {==}, Equal.cong(String, Char, zz => s_hd(zz), aa, "false", ee))),
        Equal.trans(Bool, D1.number(String.to_list(aa)), D1.number(List.append(&2, Char, String.to_list(SCon{x, t}),
          [cc])), False{}, Equal.cong(List<&2, Char>, Bool, zz => D1.number(zz), String.to_list(aa),
          List.append(&2, Char, String.to_list(SCon{x, t}), [cc]), tl_app(SCon{x, t}, cc)),
          nf_number(String.to_list(SCon{x, t}), cc, hd, M10.or_false_r(D2.digit(cc), D1.is_cp(cc, 45), hn), M9.c48(cc,
          hd), c19(cc, hd))))

# a literal name or a number with a character that is no digit after it is
# neither
law lon_snoc.at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +w: String
  for e1: {String.eq(w, "null") == b1 : Bool}
  for e2: {String.eq(w, "true") == b2 : Bool}
  for e3: {String.eq(w, "false") == b3 : Bool}
  for +h: {Bool.or(b1, Bool.or(b2, Bool.or(b3, D1.number(String.to_list(w))))) == True{} : Bool}
  {D1.lit_or_num(w ++ SCon{cc, ""}) == False{} : Bool}

def lon_snoc.at(b1, b2, b3, cc, hn, w, e1, e2, e3, h):
  match b1:
    case True{}:
      # String.eq walks to the appended character, so name its code
      match cc:
        case Chr{u}:
          ek = Equal.sym(String, w, "null", M8.str_eq_sound(w, "null", e1))
          %ek : {D1.lit_or_num(_ ++ SCon{Chr{u}, ""}) == False{} : Bool}
          {==}
    case False{}:
      match b2:
        case True{}:
          # String.eq walks to the appended character, so name its code
          match cc:
            case Chr{u}:
              ek = Equal.sym(String, w, "true", M8.str_eq_sound(w, "true", e2))
              %ek : {D1.lit_or_num(_ ++ SCon{Chr{u}, ""}) == False{} : Bool}
              {==}
        case False{}:
          match b3:
            case True{}:
              # String.eq walks to the appended character, so name its code
              match cc:
                case Chr{u}:
                  ek = Equal.sym(String, w, "false", M8.str_eq_sound(w, "false", e3))
                  %ek : {D1.lit_or_num(_ ++ SCon{Chr{u}, ""}) == False{} : Bool}
                  {==}
            case False{}:
              lon_snoc.n(cc, hn, w, h)

law lon_snoc:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +w: String
  for +h: {D1.lit_or_num(w) == True{} : Bool}
  {D1.lit_or_num(w ++ SCon{cc, ""}) == False{} : Bool}

def lon_snoc(cc, hn, w, h):
  lon_snoc.at(String.eq(w, "null"), String.eq(w, "true"), String.eq(w, "false"), cc, hn, w, {==}, {==}, {==}, h)

# a word with one more character at its end
law lon_cns:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +ba: List<&2, Char>
  for +h: {D1.lit_or_num(Lex.text(ba)) == True{} : Bool}
  {D1.lit_or_num(Lex.text(cc <> ba)) == False{} : Bool}

def lon_cns(cc, hn, ba, h):
  Equal.trans(Bool, D1.lit_or_num(Lex.text.go(ba, "" ++ SCon{cc, ""})), D1.lit_or_num(Lex.text(ba) ++ SCon{cc, ""}),
    False{}, Equal.cong(String, Bool, zz => D1.lit_or_num(zz), Lex.text.go(ba, "" ++ SCon{cc, ""}),
    Lex.text(ba) ++ SCon{cc, ""}, tg(ba, "", SCon{cc, ""})), lon_snoc(cc, hn, Lex.text(ba), h))

# laws/WhitespaceBetweenTokensIgnored.bend: an open bracket put between tokens. The scan with it is the
# scan without it one level deeper, the last token the bracket where it was
# not a value's, or it has met a fault

# what may come next, without and with the bracket
def lto(la: M3.Lt, lb: M3.Lt) -> Type:
  match la lb:
    case M3.LSt{} M3.LSt{}:
      Unit
    case M3.LSt{} M3.LOp{}:
      Unit
    case M3.LSt{} M3.LVal{}:
      Empty
    case M3.LOp{} M3.LSt{}:
      Empty
    case M3.LOp{} M3.LOp{}:
      Unit
    case M3.LOp{} M3.LVal{}:
      Empty
    case M3.LVal{} M3.LSt{}:
      Empty
    case M3.LVal{} M3.LOp{}:
      Empty
    case M3.LVal{} M3.LVal{}:
      Unit

# the scans without and with an open bracket
def rel_o(aa: M3.Sc, bb: M3.Sc) -> Type:
  match aa:
    case M3.SOut{la, da}:
      match bb:
        case M3.SOut{lb, db}:
          ({db == 1n+da : Nat} & lto(la, lb))
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SWord{ba, da}:
      match bb:
        case M3.SWord{b2, db}:
          ({db == 1n+da : Nat} & {b2 == ba : List<&2, Char>})
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SIn{da}:
      match bb:
        case M3.SIn{db}:
          {db == 1n+da : Nat}
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SEsc{da}:
      match bb:
        case M3.SEsc{db}:
          {db == 1n+da : Nat}
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SBad{}:
      Unit

# a word's end on the left, on the right, or on both
law rel_bad_o:
  for +xx: M3.Sc
  rel_o(xx, M3.SBad{})

def rel_bad_o(xx):
  match xx:
    case M3.SOut{_l, _d}:
      Unit{}
    case M3.SWord{_b, _d}:
      Unit{}
    case M3.SIn{_d}:
      Unit{}
    case M3.SEsc{_d}:
      Unit{}
    case M3.SBad{}:
      Unit{}

law pick_r_o:
  for bv: Bool
  for +xx: M3.Sc
  for +yy: M3.Sc
  for h: rel_o(xx, yy)
  rel_o(xx, Bool.pick(M3.Sc, bv, yy, M3.SBad{}))

def pick_r_o(bv, xx, _yy, h):
  match bv:
    case True{}:
      h
    case False{}:
      rel_bad_o(xx)

law pick_lr_o:
  for bv: Bool
  for +xx: M3.Sc
  for +yy: M3.Sc
  for h: rel_o(xx, yy)
  rel_o(Bool.pick(M3.Sc, bv, xx, M3.SBad{}), Bool.pick(M3.Sc, bv, yy, M3.SBad{}))

def pick_lr_o(bv, _xx, _yy, h):
  match bv:
    case True{}:
      h
    case False{}:
      Unit{}

law cl_o_oo.s.c1:
  for +da: Nat
  for +ch: Char
  rel_o(M3.sc.out(M3.LOp{}, da, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.out(M3.LOp{}, 1n+da,
      Lex.CPunct{Lex.TCloseArr{}}, ch))

def cl_o_oo.s.c1(da, _ch):
  match da:
    case 0n:
      Unit{}
    case 1n+n0:
      ({==}, Unit{})

law cl_o_oo.s.c2:
  for +da: Nat
  for +ch: Char
  rel_o(M3.sc.out(M3.LOp{}, da, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.out(M3.LOp{}, 1n+da,
      Lex.CPunct{Lex.TCloseObj{}}, ch))

def cl_o_oo.s.c2(da, _ch):
  match da:
    case 0n:
      Unit{}
    case 1n+n0:
      ({==}, Unit{})

law cl_o_oo.s.c3:
  for +da: Nat
  for +ch: Char
  rel_o(M3.sc.out(M3.LVal{}, da, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.out(M3.LVal{}, 1n+da,
      Lex.CPunct{Lex.TCloseArr{}}, ch))

def cl_o_oo.s.c3(da, _ch):
  match da:
    case 0n:
      Unit{}
    case 1n+n0:
      ({==}, Unit{})

law cl_o_oo.s.c4:
  for +da: Nat
  for +ch: Char
  rel_o(M3.sc.out(M3.LVal{}, da, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.out(M3.LVal{}, 1n+da,
      Lex.CPunct{Lex.TCloseObj{}}, ch))

def cl_o_oo.s.c4(da, _ch):
  match da:
    case 0n:
      Unit{}
    case 1n+n0:
      ({==}, Unit{})

law cl_o_oo.s:
  for +la: M3.Lt
  for +da: Nat
  for +lb: M3.Lt
  for +cls: Lex.Class
  for +ch: Char
  for l: lto(la, lb)
  rel_o(M3.sc.out(la, da, cls, ch), M3.sc.out(lb, 1n+da, cls, ch))

def cl_o_oo.s(la, da, lb, cls, ch, l):
  match la:
    case M3.LSt{}:
      match lb:
        case M3.LSt{}:
          match cls:
            case Lex.CPunct{tk}:
              match tk:
                case Lex.TOpenArr{}:
                  ({==}, Unit{})
                case Lex.TCloseArr{}:
                  Unit{}
                case Lex.TOpenObj{}:
                  ({==}, Unit{})
                case Lex.TCloseObj{}:
                  Unit{}
                case Lex.TColon{}:
                  Unit{}
                case Lex.TComma{}:
                  Unit{}
                case Lex.TStr{_x0}:
                  Unit{}
                case Lex.TWord{_x0}:
                  Unit{}
                case Lex.TStrS{_x0, _x1}:
                  Unit{}
                case Lex.TWordS{_x0, _x1}:
                  Unit{}
                case Lex.TBad{}:
                  Unit{}
            case Lex.CQuote{}:
              {==}
            case Lex.CBack{}:
              Unit{}
            case Lex.CSpace{}:
              ({==}, Unit{})
            case Lex.COther{}:
              ({==}, {==})
        case M3.LOp{}:
          match cls:
            case Lex.CPunct{tk}:
              match tk:
                case Lex.TOpenArr{}:
                  ({==}, Unit{})
                case Lex.TCloseArr{}:
                  Unit{}
                case Lex.TOpenObj{}:
                  ({==}, Unit{})
                case Lex.TCloseObj{}:
                  Unit{}
                case Lex.TColon{}:
                  Unit{}
                case Lex.TComma{}:
                  Unit{}
                case Lex.TStr{_x0}:
                  Unit{}
                case Lex.TWord{_x0}:
                  Unit{}
                case Lex.TStrS{_x0, _x1}:
                  Unit{}
                case Lex.TWordS{_x0, _x1}:
                  Unit{}
                case Lex.TBad{}:
                  Unit{}
            case Lex.CQuote{}:
              {==}
            case Lex.CBack{}:
              Unit{}
            case Lex.CSpace{}:
              ({==}, Unit{})
            case Lex.COther{}:
              ({==}, {==})
        case M3.LVal{}:
          Empty.absurd(rel_o(M3.sc.out(M3.LSt{}, da, cls, ch), M3.sc.out(M3.LVal{}, 1n+da, cls, ch)), l)
    case M3.LOp{}:
      match lb:
        case M3.LSt{}:
          Empty.absurd(rel_o(M3.sc.out(M3.LOp{}, da, cls, ch), M3.sc.out(M3.LSt{}, 1n+da, cls, ch)), l)
        case M3.LOp{}:
          match cls:
            case Lex.CPunct{tk}:
              match tk:
                case Lex.TOpenArr{}:
                  ({==}, Unit{})
                case Lex.TCloseArr{}:
                  cl_o_oo.s.c1(da, ch)
                case Lex.TOpenObj{}:
                  ({==}, Unit{})
                case Lex.TCloseObj{}:
                  cl_o_oo.s.c2(da, ch)
                case Lex.TColon{}:
                  Unit{}
                case Lex.TComma{}:
                  Unit{}
                case Lex.TStr{_x0}:
                  Unit{}
                case Lex.TWord{_x0}:
                  Unit{}
                case Lex.TStrS{_x0, _x1}:
                  Unit{}
                case Lex.TWordS{_x0, _x1}:
                  Unit{}
                case Lex.TBad{}:
                  Unit{}
            case Lex.CQuote{}:
              {==}
            case Lex.CBack{}:
              Unit{}
            case Lex.CSpace{}:
              ({==}, Unit{})
            case Lex.COther{}:
              ({==}, {==})
        case M3.LVal{}:
          Empty.absurd(rel_o(M3.sc.out(M3.LOp{}, da, cls, ch), M3.sc.out(M3.LVal{}, 1n+da, cls, ch)), l)
    case M3.LVal{}:
      match lb:
        case M3.LSt{}:
          Empty.absurd(rel_o(M3.sc.out(M3.LVal{}, da, cls, ch), M3.sc.out(M3.LSt{}, 1n+da, cls, ch)), l)
        case M3.LOp{}:
          Empty.absurd(rel_o(M3.sc.out(M3.LVal{}, da, cls, ch), M3.sc.out(M3.LOp{}, 1n+da, cls, ch)), l)
        case M3.LVal{}:
          match cls:
            case Lex.CPunct{tk}:
              match tk:
                case Lex.TOpenArr{}:
                  Unit{}
                case Lex.TCloseArr{}:
                  cl_o_oo.s.c3(da, ch)
                case Lex.TOpenObj{}:
                  Unit{}
                case Lex.TCloseObj{}:
                  cl_o_oo.s.c4(da, ch)
                case Lex.TColon{}:
                  ({==}, Unit{})
                case Lex.TComma{}:
                  ({==}, Unit{})
                case Lex.TStr{_x0}:
                  Unit{}
                case Lex.TWord{_x0}:
                  Unit{}
                case Lex.TStrS{_x0, _x1}:
                  Unit{}
                case Lex.TWordS{_x0, _x1}:
                  Unit{}
                case Lex.TBad{}:
                  Unit{}
            case Lex.CQuote{}:
              Unit{}
            case Lex.CBack{}:
              Unit{}
            case Lex.CSpace{}:
              ({==}, Unit{})
            case Lex.COther{}:
              Unit{}

law cl_o_ww.s.c1:
  for +da: Nat
  for +ba: List<&2, Char>
  for +ch: Char
  rel_o(M3.sc.word(ba, da, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.word(ba, 1n+da, Lex.CPunct{Lex.TCloseArr{}}, ch))

def cl_o_ww.s.c1(da, ba, _ch):
  match da:
    case 0n:
      pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SOut{M3.LVal{}, 0n}, Unit{})
    case 1n+n0:
      pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, n0}, M3.SOut{M3.LVal{}, 1n+n0}, ({==}, Unit{}))

law cl_o_ww.s.c2:
  for +da: Nat
  for +ba: List<&2, Char>
  for +ch: Char
  rel_o(M3.sc.word(ba, da, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.word(ba, 1n+da, Lex.CPunct{Lex.TCloseObj{}}, ch))

def cl_o_ww.s.c2(da, ba, _ch):
  match da:
    case 0n:
      pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SOut{M3.LVal{}, 0n}, Unit{})
    case 1n+n0:
      pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, n0}, M3.SOut{M3.LVal{}, 1n+n0}, ({==}, Unit{}))

law cl_o_ww.s:
  for +ba: List<&2, Char>
  for +da: Nat
  for +cls: Lex.Class
  for +ch: Char
  rel_o(M3.sc.word(ba, da, cls, ch), M3.sc.word(ba, 1n+da, cls, ch))

def cl_o_ww.s(ba, da, cls, ch):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TCloseArr{}:
          cl_o_ww.s.c1(da, ba, ch)
        case Lex.TOpenObj{}:
          pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TCloseObj{}:
          cl_o_ww.s.c2(da, ba, ch)
        case Lex.TColon{}:
          pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, da}, M3.SOut{M3.LSt{}, 1n+da}, ({==}, Unit{}))
        case Lex.TComma{}:
          pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, da}, M3.SOut{M3.LSt{}, 1n+da}, ({==}, Unit{}))
        case Lex.TStr{_x0}:
          pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TWord{_x0}:
          pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TStrS{_x0, _x1}:
          pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TWordS{_x0, _x1}:
          pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TBad{}:
          pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
    case Lex.CQuote{}:
      pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
    case Lex.CBack{}:
      pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
    case Lex.CSpace{}:
      pick_lr_o(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, da}, M3.SOut{M3.LVal{}, 1n+da}, ({==}, Unit{}))
    case Lex.COther{}:
      ({==}, {==})

law cl_o_ii.s:
  for +da: Nat
  for +cls: Lex.Class
  rel_o(M3.sc.in(da, cls), M3.sc.in(1n+da, cls))

def cl_o_ii.s(_da, cls):
  match cls:
    case Lex.CPunct{tk}:
      {==}
    case Lex.CQuote{}:
      ({==}, Unit{})
    case Lex.CBack{}:
      {==}
    case Lex.CSpace{}:
      {==}
    case Lex.COther{}:
      {==}

law cl_o_oo:
  for +la: M3.Lt
  for +da: Nat
  for +lb: M3.Lt
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_o(M3.SOut{la, da}, M3.SOut{lb, db})
  rel_o(M3.sc.out(la, da, cls, ch), M3.sc.out(lb, db, cls, ch))

def cl_o_oo(la, da, lb, db, cls, ch, h):
  (e, l) = h
  es = Equal.sym(Nat, db, 1n+da, e)
  %es : rel_o(M3.sc.out(la, da, cls, ch), M3.sc.out(lb, _, cls, ch))
  cl_o_oo.s(la, da, lb, cls, ch, l)

law cl_o_ww:
  for +ba: List<&2, Char>
  for +da: Nat
  for +b2: List<&2, Char>
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_o(M3.SWord{ba, da}, M3.SWord{b2, db})
  rel_o(M3.sc.word(ba, da, cls, ch), M3.sc.word(b2, db, cls, ch))

def cl_o_ww(ba, da, b2, db, cls, ch, h):
  (e1, e2) = h
  es1 = Equal.sym(Nat, db, 1n+da, e1)
  %es1 : rel_o(M3.sc.word(ba, da, cls, ch), M3.sc.word(b2, _, cls, ch))
  es2 = Equal.sym(List<&2, Char>, b2, ba, e2)
  %es2 : rel_o(M3.sc.word(ba, da, cls, ch), M3.sc.word(_, 1n+da, cls, ch))
  cl_o_ww.s(ba, da, cls, ch)

law cl_o_ii:
  for +da: Nat
  for +db: Nat
  for +cls: Lex.Class
  for h: rel_o(M3.SIn{da}, M3.SIn{db})
  rel_o(M3.sc.in(da, cls), M3.sc.in(db, cls))

def cl_o_ii(da, db, cls, h):
  es = Equal.sym(Nat, db, 1n+da, h)
  %es : rel_o(M3.sc.in(da, cls), M3.sc.in(_, cls))
  cl_o_ii.s(da, cls)

# one character keeps two scans related
law cl_o:
  for +aa: M3.Sc
  for +bb: M3.Sc
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_o(aa, bb)
  rel_o(M3.sc.stepc(aa, cls, ch), M3.sc.stepc(bb, cls, ch))

def cl_o(aa, bb, cls, ch, h):
  match aa bb:
    case M3.SOut{a1, a2} M3.SOut{b1, b2}:
      cl_o_oo(a1, a2, b1, b2, cls, ch, h)
    case M3.SOut{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SOut{a1, a2} M3.SIn{b1}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SOut{a1, a2} M3.SEsc{b1}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SOut{+a1, +a2} M3.SBad{}:
      rel_bad_o(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch))
    case M3.SWord{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SWord{a1, a2} M3.SWord{b1, b2}:
      cl_o_ww(a1, a2, b1, b2, cls, ch, h)
    case M3.SWord{a1, a2} M3.SIn{b1}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SWord{a1, a2} M3.SEsc{b1}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SWord{+a1, +a2} M3.SBad{}:
      rel_bad_o(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch))
    case M3.SIn{a1} M3.SOut{b1, b2}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SIn{a1} M3.SWord{b1, b2}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SIn{a1} M3.SIn{b1}:
      cl_o_ii(a1, b1, cls, h)
    case M3.SIn{a1} M3.SEsc{b1}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SIn{+a1} M3.SBad{}:
      rel_bad_o(M3.sc.stepc(M3.SIn{a1}, cls, ch))
    case M3.SEsc{a1} M3.SOut{b1, b2}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SEsc{a1} M3.SWord{b1, b2}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SEsc{a1} M3.SIn{b1}:
      Empty.absurd(rel_o(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SEsc{a1} M3.SEsc{b1}:
      h
    case M3.SEsc{+a1} M3.SBad{}:
      rel_bad_o(M3.sc.stepc(M3.SEsc{a1}, cls, ch))
    case M3.SBad{} M3.SOut{_b1, _b2}:
      Unit{}
    case M3.SBad{} M3.SWord{_b1, _b2}:
      Unit{}
    case M3.SBad{} M3.SIn{_b1}:
      Unit{}
    case M3.SBad{} M3.SEsc{_b1}:
      Unit{}
    case M3.SBad{} M3.SBad{}:
      Unit{}

law run_o:
  for +txt: String
  for +aa: M3.Sc
  for +bb: M3.Sc
  for h: rel_o(aa, bb)
  rel_o(M3.sc.run(txt, aa), M3.sc.run(txt, bb))

def run_o(txt, aa, bb, h):
  match txt:
    case SNil{}:
      h
    case SCon{+hd, +tl}:
      run_o(tl, M3.sc.step(aa, hd), M3.sc.step(bb, hd), cl_o(aa, bb, Lex.classify(hd), hd, h))

# laws/WhitespaceBetweenTokensIgnored.bend: a close bracket put between tokens. The scan without it is
# the scan with it one level deeper, the bracket where a value or a close
# could come, or a word, or it has met a fault

# what may come next, without and with the bracket
def ltc(la: M3.Lt, lb: M3.Lt) -> Type:
  match la lb:
    case M3.LSt{} M3.LSt{}:
      Unit
    case M3.LSt{} M3.LOp{}:
      Empty
    case M3.LSt{} M3.LVal{}:
      Empty
    case M3.LOp{} M3.LSt{}:
      Empty
    case M3.LOp{} M3.LOp{}:
      Unit
    case M3.LOp{} M3.LVal{}:
      Unit
    case M3.LVal{} M3.LSt{}:
      Empty
    case M3.LVal{} M3.LOp{}:
      Empty
    case M3.LVal{} M3.LVal{}:
      Unit

# what may come next after the bracket and its word: a value's end
def lv(lb: M3.Lt) -> Type:
  match lb:
    case M3.LVal{}:
      Unit
    case _:
      Empty

# the scans without and with a close bracket
def rel_c(aa: M3.Sc, bb: M3.Sc) -> Type:
  match aa:
    case M3.SOut{la, da}:
      match bb:
        case M3.SOut{lb, db}:
          ({da == 1n+db : Nat} & ltc(la, lb))
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SWord{ba, da}:
      match bb:
        case M3.SWord{b2, db}:
          ({da == 1n+db : Nat} & {b2 == ba : List<&2, Char>})
        case M3.SOut{lb, db}:
          ({da == 1n+db : Nat} & lv(lb))
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SIn{da}:
      match bb:
        case M3.SIn{db}:
          {da == 1n+db : Nat}
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SEsc{da}:
      match bb:
        case M3.SEsc{db}:
          {da == 1n+db : Nat}
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SBad{}:
      Unit

# a word's end on the left, on the right, or on both
law rel_bad_c:
  for +xx: M3.Sc
  rel_c(xx, M3.SBad{})

def rel_bad_c(xx):
  match xx:
    case M3.SOut{_l, _d}:
      Unit{}
    case M3.SWord{_b, _d}:
      Unit{}
    case M3.SIn{_d}:
      Unit{}
    case M3.SEsc{_d}:
      Unit{}
    case M3.SBad{}:
      Unit{}

law pick_l_c:
  for bv: Bool
  for +xx: M3.Sc
  for +yy: M3.Sc
  for h: rel_c(xx, yy)
  rel_c(Bool.pick(M3.Sc, bv, xx, M3.SBad{}), yy)

def pick_l_c(bv, _xx, _yy, h):
  match bv:
    case True{}:
      h
    case False{}:
      Unit{}

law pick_r_c:
  for bv: Bool
  for +xx: M3.Sc
  for +yy: M3.Sc
  for h: rel_c(xx, yy)
  rel_c(xx, Bool.pick(M3.Sc, bv, yy, M3.SBad{}))

def pick_r_c(bv, xx, _yy, h):
  match bv:
    case True{}:
      h
    case False{}:
      rel_bad_c(xx)

law pick_lr_c:
  for bv: Bool
  for +xx: M3.Sc
  for +yy: M3.Sc
  for h: rel_c(xx, yy)
  rel_c(Bool.pick(M3.Sc, bv, xx, M3.SBad{}), Bool.pick(M3.Sc, bv, yy, M3.SBad{}))

def pick_lr_c(bv, _xx, _yy, h):
  match bv:
    case True{}:
      h
    case False{}:
      Unit{}

law cl_c_oo.s.c1:
  for +db: Nat
  for +ch: Char
  rel_c(M3.sc.out(M3.LOp{}, 1n+db, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.out(M3.LOp{}, db,
      Lex.CPunct{Lex.TCloseArr{}}, ch))

def cl_c_oo.s.c1(db, _ch):
  match db:
    case 0n:
      Unit{}
    case 1n+n0:
      ({==}, Unit{})

law cl_c_oo.s.c2:
  for +db: Nat
  for +ch: Char
  rel_c(M3.sc.out(M3.LOp{}, 1n+db, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.out(M3.LOp{}, db,
      Lex.CPunct{Lex.TCloseObj{}}, ch))

def cl_c_oo.s.c2(db, _ch):
  match db:
    case 0n:
      Unit{}
    case 1n+n0:
      ({==}, Unit{})

law cl_c_oo.s.c3:
  for +db: Nat
  for +ch: Char
  rel_c(M3.sc.out(M3.LOp{}, 1n+db, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.out(M3.LVal{}, db,
      Lex.CPunct{Lex.TCloseArr{}}, ch))

def cl_c_oo.s.c3(db, _ch):
  match db:
    case 0n:
      Unit{}
    case 1n+n0:
      ({==}, Unit{})

law cl_c_oo.s.c4:
  for +db: Nat
  for +ch: Char
  rel_c(M3.sc.out(M3.LOp{}, 1n+db, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.out(M3.LVal{}, db,
      Lex.CPunct{Lex.TCloseObj{}}, ch))

def cl_c_oo.s.c4(db, _ch):
  match db:
    case 0n:
      Unit{}
    case 1n+n0:
      ({==}, Unit{})

law cl_c_oo.s.c5:
  for +db: Nat
  for +ch: Char
  rel_c(M3.sc.out(M3.LVal{}, 1n+db, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.out(M3.LVal{}, db,
      Lex.CPunct{Lex.TCloseArr{}}, ch))

def cl_c_oo.s.c5(db, _ch):
  match db:
    case 0n:
      Unit{}
    case 1n+n0:
      ({==}, Unit{})

law cl_c_oo.s.c6:
  for +db: Nat
  for +ch: Char
  rel_c(M3.sc.out(M3.LVal{}, 1n+db, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.out(M3.LVal{}, db,
      Lex.CPunct{Lex.TCloseObj{}}, ch))

def cl_c_oo.s.c6(db, _ch):
  match db:
    case 0n:
      Unit{}
    case 1n+n0:
      ({==}, Unit{})

law cl_c_oo.s:
  for +la: M3.Lt
  for +lb: M3.Lt
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  for l: ltc(la, lb)
  rel_c(M3.sc.out(la, 1n+db, cls, ch), M3.sc.out(lb, db, cls, ch))

def cl_c_oo.s(la, lb, db, cls, ch, l):
  match la:
    case M3.LSt{}:
      match lb:
        case M3.LSt{}:
          match cls:
            case Lex.CPunct{tk}:
              match tk:
                case Lex.TOpenArr{}:
                  ({==}, Unit{})
                case Lex.TCloseArr{}:
                  Unit{}
                case Lex.TOpenObj{}:
                  ({==}, Unit{})
                case Lex.TCloseObj{}:
                  Unit{}
                case Lex.TColon{}:
                  Unit{}
                case Lex.TComma{}:
                  Unit{}
                case Lex.TStr{_x0}:
                  Unit{}
                case Lex.TWord{_x0}:
                  Unit{}
                case Lex.TStrS{_x0, _x1}:
                  Unit{}
                case Lex.TWordS{_x0, _x1}:
                  Unit{}
                case Lex.TBad{}:
                  Unit{}
            case Lex.CQuote{}:
              {==}
            case Lex.CBack{}:
              Unit{}
            case Lex.CSpace{}:
              ({==}, Unit{})
            case Lex.COther{}:
              ({==}, {==})
        case M3.LOp{}:
          Empty.absurd(rel_c(M3.sc.out(M3.LSt{}, 1n+db, cls, ch), M3.sc.out(M3.LOp{}, db, cls, ch)), l)
        case M3.LVal{}:
          Empty.absurd(rel_c(M3.sc.out(M3.LSt{}, 1n+db, cls, ch), M3.sc.out(M3.LVal{}, db, cls, ch)), l)
    case M3.LOp{}:
      match lb:
        case M3.LSt{}:
          Empty.absurd(rel_c(M3.sc.out(M3.LOp{}, 1n+db, cls, ch), M3.sc.out(M3.LSt{}, db, cls, ch)), l)
        case M3.LOp{}:
          match cls:
            case Lex.CPunct{tk}:
              match tk:
                case Lex.TOpenArr{}:
                  ({==}, Unit{})
                case Lex.TCloseArr{}:
                  cl_c_oo.s.c1(db, ch)
                case Lex.TOpenObj{}:
                  ({==}, Unit{})
                case Lex.TCloseObj{}:
                  cl_c_oo.s.c2(db, ch)
                case Lex.TColon{}:
                  Unit{}
                case Lex.TComma{}:
                  Unit{}
                case Lex.TStr{_x0}:
                  Unit{}
                case Lex.TWord{_x0}:
                  Unit{}
                case Lex.TStrS{_x0, _x1}:
                  Unit{}
                case Lex.TWordS{_x0, _x1}:
                  Unit{}
                case Lex.TBad{}:
                  Unit{}
            case Lex.CQuote{}:
              {==}
            case Lex.CBack{}:
              Unit{}
            case Lex.CSpace{}:
              ({==}, Unit{})
            case Lex.COther{}:
              ({==}, {==})
        case M3.LVal{}:
          match cls:
            case Lex.CPunct{tk}:
              match tk:
                case Lex.TOpenArr{}:
                  Unit{}
                case Lex.TCloseArr{}:
                  cl_c_oo.s.c3(db, ch)
                case Lex.TOpenObj{}:
                  Unit{}
                case Lex.TCloseObj{}:
                  cl_c_oo.s.c4(db, ch)
                case Lex.TColon{}:
                  Unit{}
                case Lex.TComma{}:
                  Unit{}
                case Lex.TStr{_x0}:
                  Unit{}
                case Lex.TWord{_x0}:
                  Unit{}
                case Lex.TStrS{_x0, _x1}:
                  Unit{}
                case Lex.TWordS{_x0, _x1}:
                  Unit{}
                case Lex.TBad{}:
                  Unit{}
            case Lex.CQuote{}:
              Unit{}
            case Lex.CBack{}:
              Unit{}
            case Lex.CSpace{}:
              ({==}, Unit{})
            case Lex.COther{}:
              Unit{}
    case M3.LVal{}:
      match lb:
        case M3.LSt{}:
          Empty.absurd(rel_c(M3.sc.out(M3.LVal{}, 1n+db, cls, ch), M3.sc.out(M3.LSt{}, db, cls, ch)), l)
        case M3.LOp{}:
          Empty.absurd(rel_c(M3.sc.out(M3.LVal{}, 1n+db, cls, ch), M3.sc.out(M3.LOp{}, db, cls, ch)), l)
        case M3.LVal{}:
          match cls:
            case Lex.CPunct{tk}:
              match tk:
                case Lex.TOpenArr{}:
                  Unit{}
                case Lex.TCloseArr{}:
                  cl_c_oo.s.c5(db, ch)
                case Lex.TOpenObj{}:
                  Unit{}
                case Lex.TCloseObj{}:
                  cl_c_oo.s.c6(db, ch)
                case Lex.TColon{}:
                  ({==}, Unit{})
                case Lex.TComma{}:
                  ({==}, Unit{})
                case Lex.TStr{_x0}:
                  Unit{}
                case Lex.TWord{_x0}:
                  Unit{}
                case Lex.TStrS{_x0, _x1}:
                  Unit{}
                case Lex.TWordS{_x0, _x1}:
                  Unit{}
                case Lex.TBad{}:
                  Unit{}
            case Lex.CQuote{}:
              Unit{}
            case Lex.CBack{}:
              Unit{}
            case Lex.CSpace{}:
              ({==}, Unit{})
            case Lex.COther{}:
              Unit{}

law cl_c_ww.s.c1:
  for +db: Nat
  for +ba: List<&2, Char>
  for +ch: Char
  rel_c(M3.sc.word(ba, 1n+db, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.word(ba, db, Lex.CPunct{Lex.TCloseArr{}}, ch))

def cl_c_ww.s.c1(db, ba, _ch):
  match db:
    case 0n:
      pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, 0n}, M3.SBad{}, Unit{})
    case 1n+n0:
      pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, 1n+n0}, M3.SOut{M3.LVal{}, n0}, ({==}, Unit{}))

law cl_c_ww.s.c2:
  for +db: Nat
  for +ba: List<&2, Char>
  for +ch: Char
  rel_c(M3.sc.word(ba, 1n+db, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.word(ba, db, Lex.CPunct{Lex.TCloseObj{}}, ch))

def cl_c_ww.s.c2(db, ba, _ch):
  match db:
    case 0n:
      pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, 0n}, M3.SBad{}, Unit{})
    case 1n+n0:
      pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, 1n+n0}, M3.SOut{M3.LVal{}, n0}, ({==}, Unit{}))

law cl_c_ww.s:
  for +ba: List<&2, Char>
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  rel_c(M3.sc.word(ba, 1n+db, cls, ch), M3.sc.word(ba, db, cls, ch))

def cl_c_ww.s(ba, db, cls, ch):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TCloseArr{}:
          cl_c_ww.s.c1(db, ba, ch)
        case Lex.TOpenObj{}:
          pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TCloseObj{}:
          cl_c_ww.s.c2(db, ba, ch)
        case Lex.TColon{}:
          pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, 1n+db}, M3.SOut{M3.LSt{}, db}, ({==}, Unit{}))
        case Lex.TComma{}:
          pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, 1n+db}, M3.SOut{M3.LSt{}, db}, ({==}, Unit{}))
        case Lex.TStr{_x0}:
          pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TWord{_x0}:
          pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TStrS{_x0, _x1}:
          pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TWordS{_x0, _x1}:
          pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.TBad{}:
          pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
    case Lex.CQuote{}:
      pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
    case Lex.CBack{}:
      pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
    case Lex.CSpace{}:
      pick_lr_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, 1n+db}, M3.SOut{M3.LVal{}, db}, ({==}, Unit{}))
    case Lex.COther{}:
      ({==}, {==})

law cl_c_wo.s.c1:
  for +db: Nat
  for +ba: List<&2, Char>
  for +ch: Char
  rel_c(M3.sc.word(ba, 1n+db, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.out(M3.LVal{}, db, Lex.CPunct{Lex.TCloseArr{}},
      ch))

def cl_c_wo.s.c1(db, ba, _ch):
  match db:
    case 0n:
      pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, 0n}, M3.SBad{}, Unit{})
    case 1n+n0:
      pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, 1n+n0}, M3.SOut{M3.LVal{}, n0}, ({==}, Unit{}))

law cl_c_wo.s.c2:
  for +db: Nat
  for +ba: List<&2, Char>
  for +ch: Char
  rel_c(M3.sc.word(ba, 1n+db, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.out(M3.LVal{}, db, Lex.CPunct{Lex.TCloseObj{}},
      ch))

def cl_c_wo.s.c2(db, ba, _ch):
  match db:
    case 0n:
      pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, 0n}, M3.SBad{}, Unit{})
    case 1n+n0:
      pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, 1n+n0}, M3.SOut{M3.LVal{}, n0}, ({==}, Unit{}))

law cl_c_wo.s:
  for +ba: List<&2, Char>
  for +lb: M3.Lt
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  for l: lv(lb)
  rel_c(M3.sc.word(ba, 1n+db, cls, ch), M3.sc.out(lb, db, cls, ch))

def cl_c_wo.s(ba, lb, db, cls, ch, l):
  match lb:
    case M3.LSt{}:
      Empty.absurd(rel_c(M3.sc.word(ba, 1n+db, cls, ch), M3.sc.out(M3.LSt{}, db, cls, ch)), l)
    case M3.LOp{}:
      Empty.absurd(rel_c(M3.sc.word(ba, 1n+db, cls, ch), M3.sc.out(M3.LOp{}, db, cls, ch)), l)
    case M3.LVal{}:
      match cls:
        case Lex.CPunct{tk}:
          match tk:
            case Lex.TOpenArr{}:
              pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
            case Lex.TCloseArr{}:
              cl_c_wo.s.c1(db, ba, ch)
            case Lex.TOpenObj{}:
              pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
            case Lex.TCloseObj{}:
              cl_c_wo.s.c2(db, ba, ch)
            case Lex.TColon{}:
              pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, 1n+db}, M3.SOut{M3.LSt{}, db}, ({==}, Unit{}))
            case Lex.TComma{}:
              pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, 1n+db}, M3.SOut{M3.LSt{}, db}, ({==}, Unit{}))
            case Lex.TStr{_x0}:
              pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
            case Lex.TWord{_x0}:
              pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
            case Lex.TStrS{_x0, _x1}:
              pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
            case Lex.TWordS{_x0, _x1}:
              pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
            case Lex.TBad{}:
              pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.CQuote{}:
          pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.CBack{}:
          pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SBad{}, Unit{})
        case Lex.CSpace{}:
          pick_l_c(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, 1n+db}, M3.SOut{M3.LVal{}, db}, ({==}, Unit{}))
        case Lex.COther{}:
          Unit{}

law cl_c_ii.s:
  for +db: Nat
  for +cls: Lex.Class
  rel_c(M3.sc.in(1n+db, cls), M3.sc.in(db, cls))

def cl_c_ii.s(_db, cls):
  match cls:
    case Lex.CPunct{tk}:
      {==}
    case Lex.CQuote{}:
      ({==}, Unit{})
    case Lex.CBack{}:
      {==}
    case Lex.CSpace{}:
      {==}
    case Lex.COther{}:
      {==}

law cl_c_oo:
  for +la: M3.Lt
  for +da: Nat
  for +lb: M3.Lt
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_c(M3.SOut{la, da}, M3.SOut{lb, db})
  rel_c(M3.sc.out(la, da, cls, ch), M3.sc.out(lb, db, cls, ch))

def cl_c_oo(la, da, lb, db, cls, ch, h):
  (e, l) = h
  es = Equal.sym(Nat, da, 1n+db, e)
  %es : rel_c(M3.sc.out(la, _, cls, ch), M3.sc.out(lb, db, cls, ch))
  cl_c_oo.s(la, lb, db, cls, ch, l)

law cl_c_ww:
  for +ba: List<&2, Char>
  for +da: Nat
  for +b2: List<&2, Char>
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_c(M3.SWord{ba, da}, M3.SWord{b2, db})
  rel_c(M3.sc.word(ba, da, cls, ch), M3.sc.word(b2, db, cls, ch))

def cl_c_ww(ba, da, b2, db, cls, ch, h):
  (e1, e2) = h
  es1 = Equal.sym(Nat, da, 1n+db, e1)
  %es1 : rel_c(M3.sc.word(ba, _, cls, ch), M3.sc.word(b2, db, cls, ch))
  es2 = Equal.sym(List<&2, Char>, b2, ba, e2)
  %es2 : rel_c(M3.sc.word(ba, 1n+db, cls, ch), M3.sc.word(_, db, cls, ch))
  cl_c_ww.s(ba, db, cls, ch)

law cl_c_wo:
  for +ba: List<&2, Char>
  for +da: Nat
  for +lb: M3.Lt
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_c(M3.SWord{ba, da}, M3.SOut{lb, db})
  rel_c(M3.sc.word(ba, da, cls, ch), M3.sc.out(lb, db, cls, ch))

def cl_c_wo(ba, da, lb, db, cls, ch, h):
  (e, l) = h
  es = Equal.sym(Nat, da, 1n+db, e)
  %es : rel_c(M3.sc.word(ba, _, cls, ch), M3.sc.out(lb, db, cls, ch))
  cl_c_wo.s(ba, lb, db, cls, ch, l)

law cl_c_ii:
  for +da: Nat
  for +db: Nat
  for +cls: Lex.Class
  for h: rel_c(M3.SIn{da}, M3.SIn{db})
  rel_c(M3.sc.in(da, cls), M3.sc.in(db, cls))

def cl_c_ii(da, db, cls, h):
  es = Equal.sym(Nat, da, 1n+db, h)
  %es : rel_c(M3.sc.in(_, cls), M3.sc.in(db, cls))
  cl_c_ii.s(db, cls)

# one character keeps two scans related
law cl_c:
  for +aa: M3.Sc
  for +bb: M3.Sc
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_c(aa, bb)
  rel_c(M3.sc.stepc(aa, cls, ch), M3.sc.stepc(bb, cls, ch))

def cl_c(aa, bb, cls, ch, h):
  match aa bb:
    case M3.SOut{a1, a2} M3.SOut{b1, b2}:
      cl_c_oo(a1, a2, b1, b2, cls, ch, h)
    case M3.SOut{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd(rel_c(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SOut{a1, a2} M3.SIn{b1}:
      Empty.absurd(rel_c(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SOut{a1, a2} M3.SEsc{b1}:
      Empty.absurd(rel_c(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SOut{+a1, +a2} M3.SBad{}:
      rel_bad_c(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch))
    case M3.SWord{a1, a2} M3.SOut{b1, b2}:
      cl_c_wo(a1, a2, b1, b2, cls, ch, h)
    case M3.SWord{a1, a2} M3.SWord{b1, b2}:
      cl_c_ww(a1, a2, b1, b2, cls, ch, h)
    case M3.SWord{a1, a2} M3.SIn{b1}:
      Empty.absurd(rel_c(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SWord{a1, a2} M3.SEsc{b1}:
      Empty.absurd(rel_c(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SWord{+a1, +a2} M3.SBad{}:
      rel_bad_c(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch))
    case M3.SIn{a1} M3.SOut{b1, b2}:
      Empty.absurd(rel_c(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SIn{a1} M3.SWord{b1, b2}:
      Empty.absurd(rel_c(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SIn{a1} M3.SIn{b1}:
      cl_c_ii(a1, b1, cls, h)
    case M3.SIn{a1} M3.SEsc{b1}:
      Empty.absurd(rel_c(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SIn{+a1} M3.SBad{}:
      rel_bad_c(M3.sc.stepc(M3.SIn{a1}, cls, ch))
    case M3.SEsc{a1} M3.SOut{b1, b2}:
      Empty.absurd(rel_c(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SEsc{a1} M3.SWord{b1, b2}:
      Empty.absurd(rel_c(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SEsc{a1} M3.SIn{b1}:
      Empty.absurd(rel_c(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SEsc{a1} M3.SEsc{b1}:
      h
    case M3.SEsc{+a1} M3.SBad{}:
      rel_bad_c(M3.sc.stepc(M3.SEsc{a1}, cls, ch))
    case M3.SBad{} M3.SOut{_b1, _b2}:
      Unit{}
    case M3.SBad{} M3.SWord{_b1, _b2}:
      Unit{}
    case M3.SBad{} M3.SIn{_b1}:
      Unit{}
    case M3.SBad{} M3.SEsc{_b1}:
      Unit{}
    case M3.SBad{} M3.SBad{}:
      Unit{}

law run_c:
  for +txt: String
  for +aa: M3.Sc
  for +bb: M3.Sc
  for h: rel_c(aa, bb)
  rel_c(M3.sc.run(txt, aa), M3.sc.run(txt, bb))

def run_c(txt, aa, bb, h):
  match txt:
    case SNil{}:
      h
    case SCon{+hd, +tl}:
      run_c(tl, M3.sc.step(aa, hd), M3.sc.step(bb, hd), cl_c(aa, bb, Lex.classify(hd), hd, h))

# laws/WhitespaceBetweenTokensIgnored.bend: a comma or a colon put after a value, or anything put where
# the scan meets a fault. The scan without it is after a value, the scan with
# it waits for a value, or it has met a fault

# what may come next, without and with the separator
def lvs(la: M3.Lt, lb: M3.Lt) -> Type:
  match la lb:
    case M3.LSt{} M3.LSt{}:
      Empty
    case M3.LSt{} M3.LOp{}:
      Empty
    case M3.LSt{} M3.LVal{}:
      Empty
    case M3.LOp{} M3.LSt{}:
      Empty
    case M3.LOp{} M3.LOp{}:
      Empty
    case M3.LOp{} M3.LVal{}:
      Empty
    case M3.LVal{} M3.LSt{}:
      Unit
    case M3.LVal{} M3.LOp{}:
      Empty
    case M3.LVal{} M3.LVal{}:
      Empty

# the scans without and with a separator
def rel_s(aa: M3.Sc, bb: M3.Sc) -> Type:
  match aa:
    case M3.SOut{la, _}:
      match bb:
        case M3.SOut{lb, _}:
          lvs(la, lb)
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SBad{}:
      Unit
    case _:
      match bb:
        case M3.SBad{}:
          Unit
        case _:
          Empty

# a word's end on the left, on the right, or on both
law rel_bad_s:
  for +xx: M3.Sc
  rel_s(xx, M3.SBad{})

def rel_bad_s(xx):
  match xx:
    case M3.SOut{_l, _d}:
      Unit{}
    case M3.SWord{_b, _d}:
      Unit{}
    case M3.SIn{_d}:
      Unit{}
    case M3.SEsc{_d}:
      Unit{}
    case M3.SBad{}:
      Unit{}

law pick_r_s:
  for bv: Bool
  for +xx: M3.Sc
  for +yy: M3.Sc
  for h: rel_s(xx, yy)
  rel_s(xx, Bool.pick(M3.Sc, bv, yy, M3.SBad{}))

def pick_r_s(bv, xx, _yy, h):
  match bv:
    case True{}:
      h
    case False{}:
      rel_bad_s(xx)

law pick_lr_s:
  for bv: Bool
  for +xx: M3.Sc
  for +yy: M3.Sc
  for h: rel_s(xx, yy)
  rel_s(Bool.pick(M3.Sc, bv, xx, M3.SBad{}), Bool.pick(M3.Sc, bv, yy, M3.SBad{}))

def pick_lr_s(bv, _xx, _yy, h):
  match bv:
    case True{}:
      h
    case False{}:
      Unit{}

law cl_s_oo.s.c1:
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_s(M3.sc.out(M3.LVal{}, da, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.out(M3.LSt{}, db, Lex.CPunct{Lex.TCloseArr{}},
      ch))

def cl_s_oo.s.c1(da, _db, _ch):
  match da:
    case 0n:
      Unit{}
    case 1n+n0:
      Unit{}

law cl_s_oo.s.c2:
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_s(M3.sc.out(M3.LVal{}, da, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.out(M3.LSt{}, db, Lex.CPunct{Lex.TCloseObj{}},
      ch))

def cl_s_oo.s.c2(da, _db, _ch):
  match da:
    case 0n:
      Unit{}
    case 1n+n0:
      Unit{}

law cl_s_oo.s:
  for +la: M3.Lt
  for +da: Nat
  for +lb: M3.Lt
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  for l: lvs(la, lb)
  rel_s(M3.sc.out(la, da, cls, ch), M3.sc.out(lb, db, cls, ch))

def cl_s_oo.s(la, da, lb, db, cls, ch, l):
  match la:
    case M3.LSt{}:
      match lb:
        case M3.LSt{}:
          Empty.absurd(rel_s(M3.sc.out(M3.LSt{}, da, cls, ch), M3.sc.out(M3.LSt{}, db, cls, ch)), l)
        case M3.LOp{}:
          Empty.absurd(rel_s(M3.sc.out(M3.LSt{}, da, cls, ch), M3.sc.out(M3.LOp{}, db, cls, ch)), l)
        case M3.LVal{}:
          Empty.absurd(rel_s(M3.sc.out(M3.LSt{}, da, cls, ch), M3.sc.out(M3.LVal{}, db, cls, ch)), l)
    case M3.LOp{}:
      match lb:
        case M3.LSt{}:
          Empty.absurd(rel_s(M3.sc.out(M3.LOp{}, da, cls, ch), M3.sc.out(M3.LSt{}, db, cls, ch)), l)
        case M3.LOp{}:
          Empty.absurd(rel_s(M3.sc.out(M3.LOp{}, da, cls, ch), M3.sc.out(M3.LOp{}, db, cls, ch)), l)
        case M3.LVal{}:
          Empty.absurd(rel_s(M3.sc.out(M3.LOp{}, da, cls, ch), M3.sc.out(M3.LVal{}, db, cls, ch)), l)
    case M3.LVal{}:
      match lb:
        case M3.LSt{}:
          match cls:
            case Lex.CPunct{tk}:
              match tk:
                case Lex.TOpenArr{}:
                  Unit{}
                case Lex.TCloseArr{}:
                  cl_s_oo.s.c1(da, db, ch)
                case Lex.TOpenObj{}:
                  Unit{}
                case Lex.TCloseObj{}:
                  cl_s_oo.s.c2(da, db, ch)
                case Lex.TColon{}:
                  Unit{}
                case Lex.TComma{}:
                  Unit{}
                case Lex.TStr{_x0}:
                  Unit{}
                case Lex.TWord{_x0}:
                  Unit{}
                case Lex.TStrS{_x0, _x1}:
                  Unit{}
                case Lex.TWordS{_x0, _x1}:
                  Unit{}
                case Lex.TBad{}:
                  Unit{}
            case Lex.CQuote{}:
              Unit{}
            case Lex.CBack{}:
              Unit{}
            case Lex.CSpace{}:
              Unit{}
            case Lex.COther{}:
              Unit{}
        case M3.LOp{}:
          Empty.absurd(rel_s(M3.sc.out(M3.LVal{}, da, cls, ch), M3.sc.out(M3.LOp{}, db, cls, ch)), l)
        case M3.LVal{}:
          Empty.absurd(rel_s(M3.sc.out(M3.LVal{}, da, cls, ch), M3.sc.out(M3.LVal{}, db, cls, ch)), l)

# one character keeps two scans related
law cl_s:
  for +aa: M3.Sc
  for +bb: M3.Sc
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_s(aa, bb)
  rel_s(M3.sc.stepc(aa, cls, ch), M3.sc.stepc(bb, cls, ch))

def cl_s(aa, bb, cls, ch, h):
  match aa bb:
    case M3.SOut{a1, a2} M3.SOut{b1, b2}:
      cl_s_oo.s(a1, a2, b1, b2, cls, ch, h)
    case M3.SOut{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SOut{a1, a2} M3.SIn{b1}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SOut{a1, a2} M3.SEsc{b1}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SOut{+a1, +a2} M3.SBad{}:
      rel_bad_s(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch))
    case M3.SWord{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SWord{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SWord{a1, a2} M3.SIn{b1}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SWord{a1, a2} M3.SEsc{b1}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SWord{+a1, +a2} M3.SBad{}:
      rel_bad_s(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch))
    case M3.SIn{a1} M3.SOut{b1, b2}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SIn{a1} M3.SWord{b1, b2}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SIn{a1} M3.SIn{b1}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SIn{a1} M3.SEsc{b1}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SIn{+a1} M3.SBad{}:
      rel_bad_s(M3.sc.stepc(M3.SIn{a1}, cls, ch))
    case M3.SEsc{a1} M3.SOut{b1, b2}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SEsc{a1} M3.SWord{b1, b2}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SEsc{a1} M3.SIn{b1}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SEsc{a1} M3.SEsc{b1}:
      Empty.absurd(rel_s(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SEsc{+a1} M3.SBad{}:
      rel_bad_s(M3.sc.stepc(M3.SEsc{a1}, cls, ch))
    case M3.SBad{} M3.SOut{_b1, _b2}:
      Unit{}
    case M3.SBad{} M3.SWord{_b1, _b2}:
      Unit{}
    case M3.SBad{} M3.SIn{_b1}:
      Unit{}
    case M3.SBad{} M3.SEsc{_b1}:
      Unit{}
    case M3.SBad{} M3.SBad{}:
      Unit{}

law run_s:
  for +txt: String
  for +aa: M3.Sc
  for +bb: M3.Sc
  for h: rel_s(aa, bb)
  rel_s(M3.sc.run(txt, aa), M3.sc.run(txt, bb))

def run_s(txt, aa, bb, h):
  match txt:
    case SNil{}:
      h
    case SCon{+hd, +tl}:
      run_s(tl, M3.sc.step(aa, hd), M3.sc.step(bb, hd), cl_s(aa, bb, Lex.classify(hd), hd, h))

# laws/WhitespaceBetweenTokensIgnored.bend: a word character, not a digit or `-`, put between tokens.
# Where the scan without it waits for a value, the scan with it is in a word
# of that character; in a word, the scan with it is in the same word with the
# character in front, which no literal name or number starts with

# what may come next is not a separator or a close
def lnv(la: M3.Lt) -> Type:
  match la:
    case M3.LVal{}:
      Empty
    case _:
      Unit

# the scans without and with a word character cc
def rel_w(cc: Char, aa: M3.Sc, bb: M3.Sc) -> Type:
  match aa:
    case M3.SOut{la, _}:
      match bb:
        case M3.SWord{b2, _}:
          (lnv(la) & {b2 == [cc] : List<&2, Char>})
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SWord{ba, _}:
      match bb:
        case M3.SWord{b2, _}:
          {b2 == List.append(&2, Char, ba, [cc]) : List<&2, Char>}
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SBad{}:
      Unit
    case _:
      match bb:
        case M3.SBad{}:
          Unit
        case _:
          Empty

# a word's end on the left, on the right, or on both
law rel_bad_w:
  for +cc: Char
  for +xx: M3.Sc
  rel_w(cc, xx, M3.SBad{})

def rel_bad_w(_cc, xx):
  match xx:
    case M3.SOut{_l, _d}:
      Unit{}
    case M3.SWord{_b, _d}:
      Unit{}
    case M3.SIn{_d}:
      Unit{}
    case M3.SEsc{_d}:
      Unit{}
    case M3.SBad{}:
      Unit{}

# a word that is no literal name or number meets a fault at its end
law pick_f_w:
  for +cc: Char
  for bv: Bool
  for +xx: M3.Sc
  for +yy: M3.Sc
  for hb: {bv == False{} : Bool}
  rel_w(cc, xx, Bool.pick(M3.Sc, bv, yy, M3.SBad{}))

def pick_f_w(cc, bv, xx, yy, hb):
  es = Equal.sym(Bool, bv, False{}, hb)
  %es : rel_w(cc, xx, Bool.pick(M3.Sc, _, yy, M3.SBad{}))
  rel_bad_w(cc, xx)

# of two words, the second is none when the first is one
law pick2_w:
  for +cc: Char
  for b1: Bool
  for b2: Bool
  for +xx: M3.Sc
  for +yy: M3.Sc
  for kk: {b1 == True{} : Bool} -> {b2 == False{} : Bool}
  rel_w(cc, Bool.pick(M3.Sc, b1, xx, M3.SBad{}), Bool.pick(M3.Sc, b2, yy, M3.SBad{}))

def pick2_w(cc, b1, b2, xx, yy, kk):
  match b1:
    case True{}:
      pick_f_w(cc, b2, xx, yy, kk({==}))
    case False{}:
      Unit{}

law cl_w_ow.s.c1:
  for +db: Nat
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +da: Nat
  for +ch: Char
  rel_w(cc, M3.sc.out(M3.LSt{}, da, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.word([cc], db, Lex.CPunct{Lex.TCloseArr{}},
      ch))

def cl_w_ow.s.c1(db, cc, hn, _da, _ch):
  match db:
    case 0n:
      pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
    case 1n+n0:
      pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SOut{M3.LVal{}, n0}, lon1(cc, hn))

law cl_w_ow.s.c2:
  for +db: Nat
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +da: Nat
  for +ch: Char
  rel_w(cc, M3.sc.out(M3.LSt{}, da, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.word([cc], db, Lex.CPunct{Lex.TCloseObj{}},
      ch))

def cl_w_ow.s.c2(db, cc, hn, _da, _ch):
  match db:
    case 0n:
      pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
    case 1n+n0:
      pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SOut{M3.LVal{}, n0}, lon1(cc, hn))

law cl_w_ow.s.c3:
  for +da: Nat
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +db: Nat
  for +ch: Char
  rel_w(cc, M3.sc.out(M3.LOp{}, da, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.word([cc], db, Lex.CPunct{Lex.TCloseArr{}},
      ch))

def cl_w_ow.s.c3(da, cc, hn, db, _ch):
  match da:
    case 0n:
      match db:
        case 0n:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
        case 1n+n0:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SOut{M3.LVal{}, n0}, lon1(cc, hn))
    case 1n+n0:
      match db:
        case 0n:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SOut{M3.LVal{}, n0}, M3.SBad{}, lon1(cc, hn))
        case 1n+n1:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SOut{M3.LVal{}, n0}, M3.SOut{M3.LVal{}, n1}, lon1(cc, hn))

law cl_w_ow.s.c4:
  for +da: Nat
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +db: Nat
  for +ch: Char
  rel_w(cc, M3.sc.out(M3.LOp{}, da, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.word([cc], db, Lex.CPunct{Lex.TCloseObj{}},
      ch))

def cl_w_ow.s.c4(da, cc, hn, db, _ch):
  match da:
    case 0n:
      match db:
        case 0n:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
        case 1n+n0:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SOut{M3.LVal{}, n0}, lon1(cc, hn))
    case 1n+n0:
      match db:
        case 0n:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SOut{M3.LVal{}, n0}, M3.SBad{}, lon1(cc, hn))
        case 1n+n1:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SOut{M3.LVal{}, n0}, M3.SOut{M3.LVal{}, n1}, lon1(cc, hn))

law cl_w_ow.s:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +la: M3.Lt
  for +da: Nat
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  for l: lnv(la)
  rel_w(cc, M3.sc.out(la, da, cls, ch), M3.sc.word([cc], db, cls, ch))

def cl_w_ow.s(cc, hn, la, da, db, cls, ch, l):
  match la:
    case M3.LSt{}:
      match cls:
        case Lex.CPunct{tk}:
          match tk:
            case Lex.TOpenArr{}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SOut{M3.LOp{}, 1n+da}, M3.SBad{}, lon1(cc, hn))
            case Lex.TCloseArr{}:
              cl_w_ow.s.c1(db, cc, hn, da, ch)
            case Lex.TOpenObj{}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SOut{M3.LOp{}, 1n+da}, M3.SBad{}, lon1(cc, hn))
            case Lex.TCloseObj{}:
              cl_w_ow.s.c2(db, cc, hn, da, ch)
            case Lex.TColon{}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SOut{M3.LSt{}, db}, lon1(cc, hn))
            case Lex.TComma{}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SOut{M3.LSt{}, db}, lon1(cc, hn))
            case Lex.TStr{_x0}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
            case Lex.TWord{_x0}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
            case Lex.TStrS{_x0, _x1}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
            case Lex.TWordS{_x0, _x1}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
            case Lex.TBad{}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
        case Lex.CQuote{}:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SIn{da}, M3.SBad{}, lon1(cc, hn))
        case Lex.CBack{}:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
        case Lex.CSpace{}:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SOut{M3.LSt{}, da}, M3.SOut{M3.LVal{}, db}, lon1(cc, hn))
        case Lex.COther{}:
          {==}
    case M3.LOp{}:
      match cls:
        case Lex.CPunct{tk}:
          match tk:
            case Lex.TOpenArr{}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SOut{M3.LOp{}, 1n+da}, M3.SBad{}, lon1(cc, hn))
            case Lex.TCloseArr{}:
              cl_w_ow.s.c3(da, cc, hn, db, ch)
            case Lex.TOpenObj{}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SOut{M3.LOp{}, 1n+da}, M3.SBad{}, lon1(cc, hn))
            case Lex.TCloseObj{}:
              cl_w_ow.s.c4(da, cc, hn, db, ch)
            case Lex.TColon{}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SOut{M3.LSt{}, db}, lon1(cc, hn))
            case Lex.TComma{}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SOut{M3.LSt{}, db}, lon1(cc, hn))
            case Lex.TStr{_x0}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
            case Lex.TWord{_x0}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
            case Lex.TStrS{_x0, _x1}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
            case Lex.TWordS{_x0, _x1}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
            case Lex.TBad{}:
              pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
        case Lex.CQuote{}:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SIn{da}, M3.SBad{}, lon1(cc, hn))
        case Lex.CBack{}:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SBad{}, M3.SBad{}, lon1(cc, hn))
        case Lex.CSpace{}:
          pick_f_w(cc, D1.lit_or_num(Lex.text([cc])), M3.SOut{M3.LOp{}, da}, M3.SOut{M3.LVal{}, db}, lon1(cc, hn))
        case Lex.COther{}:
          {==}
    case M3.LVal{}:
      Empty.absurd(rel_w(cc, M3.sc.out(M3.LVal{}, da, cls, ch), M3.sc.word([cc], db, cls, ch)), l)

law cl_w_ww.s.c1:
  for +da: Nat
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +ba: List<&2, Char>
  for +db: Nat
  for +ch: Char
  rel_w(cc, M3.sc.word(ba, da, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.word(List.append(&2, Char, ba, [cc]), db,
    Lex.CPunct{Lex.TCloseArr{}}, ch))

def cl_w_ww.s.c1(da, cc, hn, ba, db, _ch):
  match da:
    case 0n:
      match db:
        case 0n:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SBad{}, M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
        case 1n+n0:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SBad{}, M3.SOut{M3.LVal{}, n0}, ee => lon_app(cc, hn, ba, ee))
    case 1n+n0:
      match db:
        case 0n:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SOut{M3.LVal{}, n0}, M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
        case 1n+n1:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SOut{M3.LVal{}, n0}, M3.SOut{M3.LVal{}, n1}, ee => lon_app(cc, hn, ba, ee))

law cl_w_ww.s.c2:
  for +da: Nat
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +ba: List<&2, Char>
  for +db: Nat
  for +ch: Char
  rel_w(cc, M3.sc.word(ba, da, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.word(List.append(&2, Char, ba, [cc]), db,
    Lex.CPunct{Lex.TCloseObj{}}, ch))

def cl_w_ww.s.c2(da, cc, hn, ba, db, _ch):
  match da:
    case 0n:
      match db:
        case 0n:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SBad{}, M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
        case 1n+n0:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SBad{}, M3.SOut{M3.LVal{}, n0}, ee => lon_app(cc, hn, ba, ee))
    case 1n+n0:
      match db:
        case 0n:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SOut{M3.LVal{}, n0}, M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
        case 1n+n1:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SOut{M3.LVal{}, n0}, M3.SOut{M3.LVal{}, n1}, ee => lon_app(cc, hn, ba, ee))

law cl_w_ww.s:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +ba: List<&2, Char>
  for +da: Nat
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  rel_w(cc, M3.sc.word(ba, da, cls, ch), M3.sc.word(List.append(&2, Char, ba, [cc]), db, cls, ch))

def cl_w_ww.s(cc, hn, ba, da, db, cls, ch):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SBad{}, M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
        case Lex.TCloseArr{}:
          cl_w_ww.s.c1(da, cc, hn, ba, db, ch)
        case Lex.TOpenObj{}:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SBad{}, M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
        case Lex.TCloseObj{}:
          cl_w_ww.s.c2(da, cc, hn, ba, db, ch)
        case Lex.TColon{}:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SOut{M3.LSt{}, da}, M3.SOut{M3.LSt{}, db}, ee => lon_app(cc, hn, ba, ee))
        case Lex.TComma{}:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SOut{M3.LSt{}, da}, M3.SOut{M3.LSt{}, db}, ee => lon_app(cc, hn, ba, ee))
        case Lex.TStr{_x0}:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SBad{}, M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
        case Lex.TWord{_x0}:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SBad{}, M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
        case Lex.TStrS{_x0, _x1}:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SBad{}, M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
        case Lex.TWordS{_x0, _x1}:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SBad{}, M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
        case Lex.TBad{}:
          pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
            M3.SBad{}, M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
    case Lex.CQuote{}:
      pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))), M3.SBad{},
        M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
    case Lex.CBack{}:
      pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))), M3.SBad{},
        M3.SBad{}, ee => lon_app(cc, hn, ba, ee))
    case Lex.CSpace{}:
      pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))),
        M3.SOut{M3.LVal{}, da}, M3.SOut{M3.LVal{}, db}, ee => lon_app(cc, hn, ba, ee))
    case Lex.COther{}:
      {==}

law cl_w_ow:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +la: M3.Lt
  for +da: Nat
  for +b2: List<&2, Char>
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_w(cc, M3.SOut{la, da}, M3.SWord{b2, db})
  rel_w(cc, M3.sc.out(la, da, cls, ch), M3.sc.word(b2, db, cls, ch))

def cl_w_ow(cc, hn, la, da, b2, db, cls, ch, h):
  (l, e) = h
  es = Equal.sym(List<&2, Char>, b2, [cc], e)
  %es : rel_w(cc, M3.sc.out(la, da, cls, ch), M3.sc.word(_, db, cls, ch))
  cl_w_ow.s(cc, hn, la, da, db, cls, ch, l)

law cl_w_ww:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +ba: List<&2, Char>
  for +da: Nat
  for +b2: List<&2, Char>
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_w(cc, M3.SWord{ba, da}, M3.SWord{b2, db})
  rel_w(cc, M3.sc.word(ba, da, cls, ch), M3.sc.word(b2, db, cls, ch))

def cl_w_ww(cc, hn, ba, da, b2, db, cls, ch, h):
  es = Equal.sym(List<&2, Char>, b2, List.append(&2, Char, ba, [cc]), h)
  %es : rel_w(cc, M3.sc.word(ba, da, cls, ch), M3.sc.word(_, db, cls, ch))
  cl_w_ww.s(cc, hn, ba, da, db, cls, ch)

# one character keeps two scans related
law cl_w:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +aa: M3.Sc
  for +bb: M3.Sc
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_w(cc, aa, bb)
  rel_w(cc, M3.sc.stepc(aa, cls, ch), M3.sc.stepc(bb, cls, ch))

def cl_w(cc, hn, aa, bb, cls, ch, h):
  match aa bb:
    case M3.SOut{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SOut{a1, a2} M3.SWord{b1, b2}:
      cl_w_ow(cc, hn, a1, a2, b1, b2, cls, ch, h)
    case M3.SOut{a1, a2} M3.SIn{b1}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SOut{a1, a2} M3.SEsc{b1}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SOut{+a1, +a2} M3.SBad{}:
      rel_bad_w(cc, M3.sc.stepc(M3.SOut{a1, a2}, cls, ch))
    case M3.SWord{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SWord{a1, a2} M3.SWord{b1, b2}:
      cl_w_ww(cc, hn, a1, a2, b1, b2, cls, ch, h)
    case M3.SWord{a1, a2} M3.SIn{b1}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SWord{a1, a2} M3.SEsc{b1}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SWord{+a1, +a2} M3.SBad{}:
      rel_bad_w(cc, M3.sc.stepc(M3.SWord{a1, a2}, cls, ch))
    case M3.SIn{a1} M3.SOut{b1, b2}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SIn{a1} M3.SWord{b1, b2}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SIn{a1} M3.SIn{b1}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SIn{a1} M3.SEsc{b1}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SIn{+a1} M3.SBad{}:
      rel_bad_w(cc, M3.sc.stepc(M3.SIn{a1}, cls, ch))
    case M3.SEsc{a1} M3.SOut{b1, b2}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SEsc{a1} M3.SWord{b1, b2}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SEsc{a1} M3.SIn{b1}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SEsc{a1} M3.SEsc{b1}:
      Empty.absurd(rel_w(cc, M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SEsc{+a1} M3.SBad{}:
      rel_bad_w(cc, M3.sc.stepc(M3.SEsc{a1}, cls, ch))
    case M3.SBad{} M3.SOut{_b1, _b2}:
      Unit{}
    case M3.SBad{} M3.SWord{_b1, _b2}:
      Unit{}
    case M3.SBad{} M3.SIn{_b1}:
      Unit{}
    case M3.SBad{} M3.SEsc{_b1}:
      Unit{}
    case M3.SBad{} M3.SBad{}:
      Unit{}

law run_w:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +txt: String
  for +aa: M3.Sc
  for +bb: M3.Sc
  for h: rel_w(cc, aa, bb)
  rel_w(cc, M3.sc.run(txt, aa), M3.sc.run(txt, bb))

def run_w(cc, hn, txt, aa, bb, h):
  match txt:
    case SNil{}:
      h
    case SCon{+hd, +tl}:
      run_w(cc, hn, tl, M3.sc.step(aa, hd), M3.sc.step(bb, hd), cl_w(cc, hn, aa, bb, Lex.classify(hd), hd, h))

# laws/WhitespaceBetweenTokensIgnored.bend: a quotation mark put between tokens. Where one scan is outside
# strings the other is in one, or it has met a fault: the two cannot both
# end outside strings

# the scans without and with a quotation mark
def rel_q(aa: M3.Sc, bb: M3.Sc) -> Type:
  match aa:
    case M3.SOut{_, _}:
      match bb:
        case M3.SIn{_}:
          Unit
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SWord{_, _}:
      match bb:
        case M3.SIn{_}:
          Unit
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SIn{_}:
      match bb:
        case M3.SOut{_, _}:
          Unit
        case M3.SWord{_, _}:
          Unit
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SEsc{_}:
      match bb:
        case M3.SBad{}:
          Unit
        case _:
          Empty
    case M3.SBad{}:
      Unit

# a word's end on the left, on the right, or on both
law rel_bad_q:
  for +xx: M3.Sc
  rel_q(xx, M3.SBad{})

def rel_bad_q(xx):
  match xx:
    case M3.SOut{_l, _d}:
      Unit{}
    case M3.SWord{_b, _d}:
      Unit{}
    case M3.SIn{_d}:
      Unit{}
    case M3.SEsc{_d}:
      Unit{}
    case M3.SBad{}:
      Unit{}

law pick_l_q:
  for bv: Bool
  for +xx: M3.Sc
  for +yy: M3.Sc
  for h: rel_q(xx, yy)
  rel_q(Bool.pick(M3.Sc, bv, xx, M3.SBad{}), yy)

def pick_l_q(bv, _xx, _yy, h):
  match bv:
    case True{}:
      h
    case False{}:
      Unit{}

law pick_r_q:
  for bv: Bool
  for +xx: M3.Sc
  for +yy: M3.Sc
  for h: rel_q(xx, yy)
  rel_q(xx, Bool.pick(M3.Sc, bv, yy, M3.SBad{}))

def pick_r_q(bv, xx, _yy, h):
  match bv:
    case True{}:
      h
    case False{}:
      rel_bad_q(xx)

law cl_q_oi.s.c1:
  for +la: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.out(la, da, Lex.CPunct{Lex.TOpenArr{}}, ch), M3.sc.in(db, Lex.CPunct{Lex.TOpenArr{}}))

def cl_q_oi.s.c1(la, _da, _db, _ch):
  match la:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_oi.s.c2:
  for +la: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.out(la, da, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.in(db, Lex.CPunct{Lex.TCloseArr{}}))

def cl_q_oi.s.c2(la, da, _db, _ch):
  match la:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      match da:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}
    case M3.LVal{}:
      match da:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}

law cl_q_oi.s.c3:
  for +la: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.out(la, da, Lex.CPunct{Lex.TOpenObj{}}, ch), M3.sc.in(db, Lex.CPunct{Lex.TOpenObj{}}))

def cl_q_oi.s.c3(la, _da, _db, _ch):
  match la:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_oi.s.c4:
  for +la: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.out(la, da, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.in(db, Lex.CPunct{Lex.TCloseObj{}}))

def cl_q_oi.s.c4(la, da, _db, _ch):
  match la:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      match da:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}
    case M3.LVal{}:
      match da:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}

law cl_q_oi.s.c5:
  for +la: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.out(la, da, Lex.CPunct{Lex.TColon{}}, ch), M3.sc.in(db, Lex.CPunct{Lex.TColon{}}))

def cl_q_oi.s.c5(la, _da, _db, _ch):
  match la:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_oi.s.c6:
  for +la: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.out(la, da, Lex.CPunct{Lex.TComma{}}, ch), M3.sc.in(db, Lex.CPunct{Lex.TComma{}}))

def cl_q_oi.s.c6(la, _da, _db, _ch):
  match la:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_oi.s.c7:
  for +la: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.out(la, da, Lex.CQuote{}, ch), M3.sc.in(db, Lex.CQuote{}))

def cl_q_oi.s.c7(la, _da, _db, _ch):
  match la:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_oi.s.c8:
  for +la: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.out(la, da, Lex.COther{}, ch), M3.sc.in(db, Lex.COther{}))

def cl_q_oi.s.c8(la, _da, _db, _ch):
  match la:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_oi.s:
  for +la: M3.Lt
  for +da: Nat
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  rel_q(M3.sc.out(la, da, cls, ch), M3.sc.in(db, cls))

def cl_q_oi.s(la, da, db, cls, ch):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          cl_q_oi.s.c1(la, da, db, ch)
        case Lex.TCloseArr{}:
          cl_q_oi.s.c2(la, da, db, ch)
        case Lex.TOpenObj{}:
          cl_q_oi.s.c3(la, da, db, ch)
        case Lex.TCloseObj{}:
          cl_q_oi.s.c4(la, da, db, ch)
        case Lex.TColon{}:
          cl_q_oi.s.c5(la, da, db, ch)
        case Lex.TComma{}:
          cl_q_oi.s.c6(la, da, db, ch)
        case Lex.TStr{_x0}:
          Unit{}
        case Lex.TWord{_x0}:
          Unit{}
        case Lex.TStrS{_x0, _x1}:
          Unit{}
        case Lex.TWordS{_x0, _x1}:
          Unit{}
        case Lex.TBad{}:
          Unit{}
    case Lex.CQuote{}:
      cl_q_oi.s.c7(la, da, db, ch)
    case Lex.CBack{}:
      Unit{}
    case Lex.CSpace{}:
      Unit{}
    case Lex.COther{}:
      cl_q_oi.s.c8(la, da, db, ch)

law cl_q_wi.s.c1:
  for +da: Nat
  for +ba: List<&2, Char>
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.word(ba, da, Lex.CPunct{Lex.TCloseArr{}}, ch), M3.sc.in(db, Lex.CPunct{Lex.TCloseArr{}}))

def cl_q_wi.s.c1(da, ba, db, _ch):
  match da:
    case 0n:
      pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SIn{db}, Unit{})
    case 1n+n0:
      pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, n0}, M3.SIn{db}, Unit{})

law cl_q_wi.s.c2:
  for +da: Nat
  for +ba: List<&2, Char>
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.word(ba, da, Lex.CPunct{Lex.TCloseObj{}}, ch), M3.sc.in(db, Lex.CPunct{Lex.TCloseObj{}}))

def cl_q_wi.s.c2(da, ba, db, _ch):
  match da:
    case 0n:
      pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SIn{db}, Unit{})
    case 1n+n0:
      pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, n0}, M3.SIn{db}, Unit{})

law cl_q_wi.s:
  for +ba: List<&2, Char>
  for +da: Nat
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  rel_q(M3.sc.word(ba, da, cls, ch), M3.sc.in(db, cls))

def cl_q_wi.s(ba, da, db, cls, ch):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SIn{db}, Unit{})
        case Lex.TCloseArr{}:
          cl_q_wi.s.c1(da, ba, db, ch)
        case Lex.TOpenObj{}:
          pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SIn{db}, Unit{})
        case Lex.TCloseObj{}:
          cl_q_wi.s.c2(da, ba, db, ch)
        case Lex.TColon{}:
          pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, da}, M3.SIn{db}, Unit{})
        case Lex.TComma{}:
          pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, da}, M3.SIn{db}, Unit{})
        case Lex.TStr{_x0}:
          pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SIn{db}, Unit{})
        case Lex.TWord{_x0}:
          pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SIn{db}, Unit{})
        case Lex.TStrS{_x0, _x1}:
          pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SIn{db}, Unit{})
        case Lex.TWordS{_x0, _x1}:
          pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SIn{db}, Unit{})
        case Lex.TBad{}:
          pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SIn{db}, Unit{})
    case Lex.CQuote{}:
      pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SOut{M3.LVal{}, db}, Unit{})
    case Lex.CBack{}:
      pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, M3.SEsc{db}, Unit{})
    case Lex.CSpace{}:
      pick_l_q(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, da}, M3.SIn{db}, Unit{})
    case Lex.COther{}:
      Unit{}

law cl_q_io.s.c1:
  for +lb: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.in(da, Lex.CPunct{Lex.TOpenArr{}}), M3.sc.out(lb, db, Lex.CPunct{Lex.TOpenArr{}}, ch))

def cl_q_io.s.c1(lb, _da, _db, _ch):
  match lb:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_io.s.c2:
  for +lb: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.in(da, Lex.CPunct{Lex.TCloseArr{}}), M3.sc.out(lb, db, Lex.CPunct{Lex.TCloseArr{}}, ch))

def cl_q_io.s.c2(lb, _da, db, _ch):
  match lb:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      match db:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}
    case M3.LVal{}:
      match db:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}

law cl_q_io.s.c3:
  for +lb: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.in(da, Lex.CPunct{Lex.TOpenObj{}}), M3.sc.out(lb, db, Lex.CPunct{Lex.TOpenObj{}}, ch))

def cl_q_io.s.c3(lb, _da, _db, _ch):
  match lb:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_io.s.c4:
  for +lb: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.in(da, Lex.CPunct{Lex.TCloseObj{}}), M3.sc.out(lb, db, Lex.CPunct{Lex.TCloseObj{}}, ch))

def cl_q_io.s.c4(lb, _da, db, _ch):
  match lb:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      match db:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}
    case M3.LVal{}:
      match db:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}

law cl_q_io.s.c5:
  for +lb: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.in(da, Lex.CPunct{Lex.TColon{}}), M3.sc.out(lb, db, Lex.CPunct{Lex.TColon{}}, ch))

def cl_q_io.s.c5(lb, _da, _db, _ch):
  match lb:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_io.s.c6:
  for +lb: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.in(da, Lex.CPunct{Lex.TComma{}}), M3.sc.out(lb, db, Lex.CPunct{Lex.TComma{}}, ch))

def cl_q_io.s.c6(lb, _da, _db, _ch):
  match lb:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_io.s.c7:
  for +lb: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.in(da, Lex.CQuote{}), M3.sc.out(lb, db, Lex.CQuote{}, ch))

def cl_q_io.s.c7(lb, _da, _db, _ch):
  match lb:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_io.s.c8:
  for +lb: M3.Lt
  for +da: Nat
  for +db: Nat
  for +ch: Char
  rel_q(M3.sc.in(da, Lex.COther{}), M3.sc.out(lb, db, Lex.COther{}, ch))

def cl_q_io.s.c8(lb, _da, _db, _ch):
  match lb:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cl_q_io.s:
  for +da: Nat
  for +lb: M3.Lt
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  rel_q(M3.sc.in(da, cls), M3.sc.out(lb, db, cls, ch))

def cl_q_io.s(da, lb, db, cls, ch):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          cl_q_io.s.c1(lb, da, db, ch)
        case Lex.TCloseArr{}:
          cl_q_io.s.c2(lb, da, db, ch)
        case Lex.TOpenObj{}:
          cl_q_io.s.c3(lb, da, db, ch)
        case Lex.TCloseObj{}:
          cl_q_io.s.c4(lb, da, db, ch)
        case Lex.TColon{}:
          cl_q_io.s.c5(lb, da, db, ch)
        case Lex.TComma{}:
          cl_q_io.s.c6(lb, da, db, ch)
        case Lex.TStr{_x0}:
          Unit{}
        case Lex.TWord{_x0}:
          Unit{}
        case Lex.TStrS{_x0, _x1}:
          Unit{}
        case Lex.TWordS{_x0, _x1}:
          Unit{}
        case Lex.TBad{}:
          Unit{}
    case Lex.CQuote{}:
      cl_q_io.s.c7(lb, da, db, ch)
    case Lex.CBack{}:
      Unit{}
    case Lex.CSpace{}:
      Unit{}
    case Lex.COther{}:
      cl_q_io.s.c8(lb, da, db, ch)

law cl_q_iw.s.c1:
  for +db: Nat
  for +da: Nat
  for +b2: List<&2, Char>
  for +ch: Char
  rel_q(M3.sc.in(da, Lex.CPunct{Lex.TCloseArr{}}), M3.sc.word(b2, db, Lex.CPunct{Lex.TCloseArr{}}, ch))

def cl_q_iw.s.c1(db, da, b2, _ch):
  match db:
    case 0n:
      pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SBad{}, Unit{})
    case 1n+n0:
      pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SOut{M3.LVal{}, n0}, Unit{})

law cl_q_iw.s.c2:
  for +db: Nat
  for +da: Nat
  for +b2: List<&2, Char>
  for +ch: Char
  rel_q(M3.sc.in(da, Lex.CPunct{Lex.TCloseObj{}}), M3.sc.word(b2, db, Lex.CPunct{Lex.TCloseObj{}}, ch))

def cl_q_iw.s.c2(db, da, b2, _ch):
  match db:
    case 0n:
      pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SBad{}, Unit{})
    case 1n+n0:
      pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SOut{M3.LVal{}, n0}, Unit{})

law cl_q_iw.s:
  for +da: Nat
  for +b2: List<&2, Char>
  for +db: Nat
  for +cls: Lex.Class
  for +ch: Char
  rel_q(M3.sc.in(da, cls), M3.sc.word(b2, db, cls, ch))

def cl_q_iw.s(da, b2, db, cls, ch):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SBad{}, Unit{})
        case Lex.TCloseArr{}:
          cl_q_iw.s.c1(db, da, b2, ch)
        case Lex.TOpenObj{}:
          pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SBad{}, Unit{})
        case Lex.TCloseObj{}:
          cl_q_iw.s.c2(db, da, b2, ch)
        case Lex.TColon{}:
          pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SOut{M3.LSt{}, db}, Unit{})
        case Lex.TComma{}:
          pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SOut{M3.LSt{}, db}, Unit{})
        case Lex.TStr{_x0}:
          pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SBad{}, Unit{})
        case Lex.TWord{_x0}:
          pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SBad{}, Unit{})
        case Lex.TStrS{_x0, _x1}:
          pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SBad{}, Unit{})
        case Lex.TWordS{_x0, _x1}:
          pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SBad{}, Unit{})
        case Lex.TBad{}:
          pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SBad{}, Unit{})
    case Lex.CQuote{}:
      pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SOut{M3.LVal{}, da}, M3.SBad{}, Unit{})
    case Lex.CBack{}:
      pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SEsc{da}, M3.SBad{}, Unit{})
    case Lex.CSpace{}:
      pick_r_q(D1.lit_or_num(Lex.text(b2)), M3.SIn{da}, M3.SOut{M3.LVal{}, db}, Unit{})
    case Lex.COther{}:
      Unit{}

# one character keeps two scans related
law cl_q:
  for +aa: M3.Sc
  for +bb: M3.Sc
  for +cls: Lex.Class
  for +ch: Char
  for h: rel_q(aa, bb)
  rel_q(M3.sc.stepc(aa, cls, ch), M3.sc.stepc(bb, cls, ch))

def cl_q(aa, bb, cls, ch, h):
  match aa bb:
    case M3.SOut{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SOut{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SOut{a1, a2} M3.SIn{b1}:
      cl_q_oi.s(a1, a2, b1, cls, ch)
    case M3.SOut{a1, a2} M3.SEsc{b1}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SOut{+a1, +a2} M3.SBad{}:
      rel_bad_q(M3.sc.stepc(M3.SOut{a1, a2}, cls, ch))
    case M3.SWord{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SWord{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SWord{a1, a2} M3.SIn{b1}:
      cl_q_wi.s(a1, a2, b1, cls, ch)
    case M3.SWord{a1, a2} M3.SEsc{b1}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SWord{+a1, +a2} M3.SBad{}:
      rel_bad_q(M3.sc.stepc(M3.SWord{a1, a2}, cls, ch))
    case M3.SIn{a1} M3.SOut{b1, b2}:
      cl_q_io.s(a1, b1, b2, cls, ch)
    case M3.SIn{a1} M3.SWord{b1, b2}:
      cl_q_iw.s(a1, b1, b2, cls, ch)
    case M3.SIn{a1} M3.SIn{b1}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SIn{a1} M3.SEsc{b1}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SIn{a1}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SIn{+a1} M3.SBad{}:
      rel_bad_q(M3.sc.stepc(M3.SIn{a1}, cls, ch))
    case M3.SEsc{a1} M3.SOut{b1, b2}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SOut{b1, b2}, cls, ch)), h)
    case M3.SEsc{a1} M3.SWord{b1, b2}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SWord{b1, b2}, cls, ch)), h)
    case M3.SEsc{a1} M3.SIn{b1}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SIn{b1}, cls, ch)), h)
    case M3.SEsc{a1} M3.SEsc{b1}:
      Empty.absurd(rel_q(M3.sc.stepc(M3.SEsc{a1}, cls, ch), M3.sc.stepc(M3.SEsc{b1}, cls, ch)), h)
    case M3.SEsc{+a1} M3.SBad{}:
      rel_bad_q(M3.sc.stepc(M3.SEsc{a1}, cls, ch))
    case M3.SBad{} M3.SOut{_b1, _b2}:
      Unit{}
    case M3.SBad{} M3.SWord{_b1, _b2}:
      Unit{}
    case M3.SBad{} M3.SIn{_b1}:
      Unit{}
    case M3.SBad{} M3.SEsc{_b1}:
      Unit{}
    case M3.SBad{} M3.SBad{}:
      Unit{}

law run_q:
  for +txt: String
  for +aa: M3.Sc
  for +bb: M3.Sc
  for h: rel_q(aa, bb)
  rel_q(M3.sc.run(txt, aa), M3.sc.run(txt, bb))

def run_q(txt, aa, bb, h):
  match txt:
    case SNil{}:
      h
    case SCon{+hd, +tl}:
      run_q(tl, M3.sc.step(aa, hd), M3.sc.step(bb, hd), cl_q(aa, bb, Lex.classify(hd), hd, h))

# laws/WhitespaceBetweenTokensIgnored.bend: where two related scans end

# after a value one level deeper, the scan is not at the top level
law topo_s:
  for +lt: M3.Lt
  for +nn: Nat
  {M3.sc.top.o(lt, 1n+nn) == False{} : Bool}

def topo_s(lt, _nn):
  match lt:
    case M3.LSt{}:
      {==}
    case M3.LOp{}:
      {==}
    case M3.LVal{}:
      {==}

law top_pick_s:
  for bv: Bool
  for +nn: Nat
  {M3.sc.top(Bool.pick(M3.Sc, bv, M3.SOut{M3.LVal{}, 1n+nn}, M3.SBad{})) == False{} : Bool}

def top_pick_s(bv, _nn):
  match bv:
    case True{}:
      {==}
    case False{}:
      {==}

# a word the scan accepts at its end is a literal name or a number
law tpt:
  for bv: Bool
  for +dd: Nat
  for h: {M3.sc.top(Bool.pick(M3.Sc, bv, M3.SOut{M3.LVal{}, dd}, M3.SBad{})) == True{} : Bool}
  {bv == True{} : Bool}

def tpt(bv, _dd, h):
  match bv:
    case True{}:
      {==}
    case False{}:
      M6.no({False{} == True{} : Bool}, h)

# a scan waiting for a value is not accepted
law acc_pst:
  for bv: Bool
  for +dd: Nat
  {M3.sc.acc(Bool.pick(M3.Sc, bv, M3.SOut{M3.LSt{}, dd}, M3.SBad{})) == False{} : Bool}

def acc_pst(bv, _dd):
  match bv:
    case True{}:
      {==}
    case False{}:
      {==}

# a scan outside strings, in a word or past a fault
def bnd(st: M3.Sc) -> Type:
  match st:
    case M3.SIn{_}:
      Empty
    case M3.SEsc{_}:
      Empty
    case _:
      Unit

# after a word, what follows it is no word character
def gw(post: String) -> Type:
  match post:
    case SNil{}:
      Unit
    case SCon{hd, _}:
      {M3.is_oth(Lex.classify(hd)) == False{} : Bool}

def gapw(st: M3.Sc, post: String) -> Type:
  match st:
    case M3.SWord{_, _}:
      gw(post)
    case _:
      Unit

law acc_o_oo:
  for +la: M3.Lt
  for +da: Nat
  for +lb: M3.Lt
  for +db: Nat
  for h: rel_o(M3.SOut{la, da}, M3.SOut{lb, db})
  {M3.sc.top.o(lb, db) == False{} : Bool}

def acc_o_oo(_la, da, lb, db, h):
  (e, _l) = h
  es = Equal.sym(Nat, db, 1n+da, e)
  %es : {M3.sc.top.o(lb, _) == False{} : Bool}
  topo_s(lb, da)

law acc_o_ww:
  for +ba: List<&2, Char>
  for +da: Nat
  for +b2: List<&2, Char>
  for +db: Nat
  for h: rel_o(M3.SWord{ba, da}, M3.SWord{b2, db})
  {M3.sc.top(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(b2)), M3.SOut{M3.LVal{}, db}, M3.SBad{})) == False{} : Bool}

def acc_o_ww(_ba, da, b2, db, h):
  (e, _e2) = h
  es = Equal.sym(Nat, db, 1n+da, e)
  %es : {M3.sc.top(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(b2)), M3.SOut{M3.LVal{}, _}, M3.SBad{})) == False{} : Bool}
  top_pick_s(D1.lit_or_num(Lex.text(b2)), da)

# a scan related to one the scan accepts is not accepted
law acc_o:
  for +aa: M3.Sc
  for +bb: M3.Sc
  for h: rel_o(aa, bb)
  for ha: {M3.sc.acc(aa) == True{} : Bool}
  {M3.sc.acc(bb) == False{} : Bool}

def acc_o(aa, bb, h, ha):
  match aa bb:
    case M3.SOut{a1, a2} M3.SOut{b1, b2}:
      acc_o_oo(a1, a2, b1, b2, h)
    case M3.SOut{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SOut{a1, a2} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SOut{a1, a2} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SOut{_a1, _a2} M3.SBad{}:
      {==}
    case M3.SWord{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SWord{a1, a2} M3.SWord{b1, b2}:
      acc_o_ww(a1, a2, b1, b2, h)
    case M3.SWord{a1, a2} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SWord{a1, a2} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SWord{_a1, _a2} M3.SBad{}:
      {==}
    case M3.SIn{a1} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SIn{a1} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SIn{a1} M3.SIn{b1}:
      {==}
    case M3.SIn{a1} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SIn{_a1} M3.SBad{}:
      {==}
    case M3.SEsc{a1} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SEsc{b1}:
      {==}
    case M3.SEsc{_a1} M3.SBad{}:
      {==}
    case M3.SBad{} M3.SOut{b1, b2}:
      M6.no({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SWord{b1, b2}:
      M6.no({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SIn{b1}:
      M6.no({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SEsc{b1}:
      M6.no({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SBad{}:
      M6.no({M3.sc.acc(M3.SBad{}) == False{} : Bool}, ha)

law acc_c_o:
  for +la: M3.Lt
  for +da: Nat
  for +db: Nat
  for e: {da == 1n+db : Nat}
  for ha: {M3.sc.top.o(la, da) == True{} : Bool}
  Empty

def acc_c_o(la, da, db, e, ha):
  M1.true_false(Equal.trans(Bool, True{}, M3.sc.top.o(la, da), False{}, Equal.sym(Bool, M3.sc.top.o(la, da), True{},
      ha),
    Equal.trans(Bool, M3.sc.top.o(la, da), M3.sc.top.o(la, 1n+db), False{}, Equal.cong(Nat, Bool, zz => M3.sc.top.o(la,
        zz), da,
    1n+db, e), topo_s(la, db))))

law acc_c_w:
  for bv: Bool
  for +da: Nat
  for +db: Nat
  for e: {da == 1n+db : Nat}
  for ha: {M3.sc.top(Bool.pick(M3.Sc, bv, M3.SOut{M3.LVal{}, da}, M3.SBad{})) == True{} : Bool}
  Empty

def acc_c_w(bv, da, db, e, ha):
  M1.true_false(Equal.trans(Bool, True{}, M3.sc.top(Bool.pick(M3.Sc, bv, M3.SOut{M3.LVal{}, da}, M3.SBad{})), False{},
      Equal.sym(Bool,
    M3.sc.top(Bool.pick(M3.Sc, bv, M3.SOut{M3.LVal{}, da}, M3.SBad{})), True{}, ha), Equal.trans(Bool,
        M3.sc.top(Bool.pick(M3.Sc, bv,
    M3.SOut{M3.LVal{}, da}, M3.SBad{})), M3.sc.top(Bool.pick(M3.Sc, bv, M3.SOut{M3.LVal{}, 1n+db}, M3.SBad{})),
        False{}, Equal.cong(Nat, Bool,
    zz => M3.sc.top(Bool.pick(M3.Sc, bv, M3.SOut{M3.LVal{}, zz}, M3.SBad{})), da, 1n+db, e), top_pick_s(bv, db))))

law acc_c_oo:
  for +la: M3.Lt
  for +da: Nat
  for +lb: M3.Lt
  for +db: Nat
  for h: rel_c(M3.SOut{la, da}, M3.SOut{lb, db})
  for ha: {M3.sc.top.o(la, da) == True{} : Bool}
  Empty

def acc_c_oo(la, da, _lb, db, h, ha):
  (e, _l) = h
  acc_c_o(la, da, db, e, ha)

law acc_c_ww:
  for +ba: List<&2, Char>
  for +da: Nat
  for +b2: List<&2, Char>
  for +db: Nat
  for h: rel_c(M3.SWord{ba, da}, M3.SWord{b2, db})
  for ha: {M3.sc.top(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, da}, M3.SBad{})) == True{} : Bool}
  Empty

def acc_c_ww(ba, da, _b2, db, h, ha):
  (e, _l) = h
  acc_c_w(D1.lit_or_num(Lex.text(ba)), da, db, e, ha)

law acc_c_wo:
  for +ba: List<&2, Char>
  for +da: Nat
  for +lb: M3.Lt
  for +db: Nat
  for h: rel_c(M3.SWord{ba, da}, M3.SOut{lb, db})
  for ha: {M3.sc.top(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, da}, M3.SBad{})) == True{} : Bool}
  Empty

def acc_c_wo(ba, da, _lb, db, h, ha):
  (e, _l) = h
  acc_c_w(D1.lit_or_num(Lex.text(ba)), da, db, e, ha)

# a scan related to one the scan accepts is not accepted
law acc_c:
  for +aa: M3.Sc
  for +bb: M3.Sc
  for h: rel_c(aa, bb)
  for ha: {M3.sc.acc(aa) == True{} : Bool}
  {M3.sc.acc(bb) == False{} : Bool}

def acc_c(aa, bb, h, ha):
  match aa bb:
    case M3.SOut{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, acc_c_oo(a1, a2, b1, b2, h, ha))
    case M3.SOut{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SOut{a1, a2} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SOut{a1, a2} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SOut{_a1, _a2} M3.SBad{}:
      {==}
    case M3.SWord{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, acc_c_wo(a1, a2, b1, b2, h, ha))
    case M3.SWord{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, acc_c_ww(a1, a2, b1, b2, h, ha))
    case M3.SWord{a1, a2} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SWord{a1, a2} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SWord{_a1, _a2} M3.SBad{}:
      {==}
    case M3.SIn{a1} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SIn{a1} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SIn{a1} M3.SIn{b1}:
      {==}
    case M3.SIn{a1} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SIn{_a1} M3.SBad{}:
      {==}
    case M3.SEsc{a1} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SEsc{b1}:
      {==}
    case M3.SEsc{_a1} M3.SBad{}:
      {==}
    case M3.SBad{} M3.SOut{b1, b2}:
      M6.no({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SWord{b1, b2}:
      M6.no({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SIn{b1}:
      M6.no({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SEsc{b1}:
      M6.no({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SBad{}:
      M6.no({M3.sc.acc(M3.SBad{}) == False{} : Bool}, ha)

law acc_s_oo:
  for +la: M3.Lt
  for +lb: M3.Lt
  for +db: Nat
  for l: lvs(la, lb)
  {M3.sc.top.o(lb, db) == False{} : Bool}

def acc_s_oo(la, lb, db, l):
  match la lb:
    case M3.LSt{} M3.LSt{}:
      Empty.absurd({M3.sc.top.o(M3.LSt{}, db) == False{} : Bool}, l)
    case M3.LSt{} M3.LOp{}:
      Empty.absurd({M3.sc.top.o(M3.LOp{}, db) == False{} : Bool}, l)
    case M3.LSt{} M3.LVal{}:
      Empty.absurd({M3.sc.top.o(M3.LVal{}, db) == False{} : Bool}, l)
    case M3.LOp{} M3.LSt{}:
      Empty.absurd({M3.sc.top.o(M3.LSt{}, db) == False{} : Bool}, l)
    case M3.LOp{} M3.LOp{}:
      Empty.absurd({M3.sc.top.o(M3.LOp{}, db) == False{} : Bool}, l)
    case M3.LOp{} M3.LVal{}:
      Empty.absurd({M3.sc.top.o(M3.LVal{}, db) == False{} : Bool}, l)
    case M3.LVal{} M3.LSt{}:
      {==}
    case M3.LVal{} M3.LOp{}:
      Empty.absurd({M3.sc.top.o(M3.LOp{}, db) == False{} : Bool}, l)
    case M3.LVal{} M3.LVal{}:
      Empty.absurd({M3.sc.top.o(M3.LVal{}, db) == False{} : Bool}, l)

# a scan related to one the scan accepts is not accepted
law acc_s:
  for +aa: M3.Sc
  for +bb: M3.Sc
  for h: rel_s(aa, bb)
  for ha: {M3.sc.acc(aa) == True{} : Bool}
  {M3.sc.acc(bb) == False{} : Bool}

def acc_s(aa, bb, h, ha):
  match aa bb:
    case M3.SOut{a1, a2} M3.SOut{b1, b2}:
      acc_s_oo(a1, b1, b2, h)
    case M3.SOut{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SOut{a1, a2} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SOut{a1, a2} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SOut{_a1, _a2} M3.SBad{}:
      {==}
    case M3.SWord{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SWord{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SWord{a1, a2} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SWord{a1, a2} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SWord{_a1, _a2} M3.SBad{}:
      {==}
    case M3.SIn{a1} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SIn{a1} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SIn{a1} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SIn{a1} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SIn{_a1} M3.SBad{}:
      {==}
    case M3.SEsc{a1} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SEsc{_a1} M3.SBad{}:
      {==}
    case M3.SBad{} M3.SOut{b1, b2}:
      M6.no({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SWord{b1, b2}:
      M6.no({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SIn{b1}:
      M6.no({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SEsc{b1}:
      M6.no({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SBad{}:
      M6.no({M3.sc.acc(M3.SBad{}) == False{} : Bool}, ha)

law acc_w_o:
  for +la: M3.Lt
  for +da: Nat
  for l: lnv(la)
  for ha: {M3.sc.top.o(la, da) == True{} : Bool}
  Empty

def acc_w_o(la, _da, l, ha):
  match la:
    case M3.LSt{}:
      M6.false_true(ha)
    case M3.LOp{}:
      M6.false_true(ha)
    case M3.LVal{}:
      l

law acc_w_ow:
  for +la: M3.Lt
  for +da: Nat
  for +b2: List<&2, Char>
  for +db: Nat
  for +cc: Char
  for h: rel_w(cc, M3.SOut{la, da}, M3.SWord{b2, db})
  for ha: {M3.sc.top.o(la, da) == True{} : Bool}
  Empty

def acc_w_ow(la, da, _b2, _db, _cc, h, ha):
  (l, _e) = h
  acc_w_o(la, da, l, ha)

law acc_w_ww:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +ba: List<&2, Char>
  for +da: Nat
  for +b2: List<&2, Char>
  for +db: Nat
  for h: {b2 == List.append(&2, Char, ba, [cc]) : List<&2, Char>}
  for ha: {M3.sc.top(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, da}, M3.SBad{})) == True{} : Bool}
  {M3.sc.top(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(b2)), M3.SOut{M3.LVal{}, db}, M3.SBad{})) == False{} : Bool}

def acc_w_ww(cc, hn, ba, da, b2, db, h, ha):
  hs = Equal.sym(List<&2, Char>, b2, List.append(&2, Char, ba, [cc]), h)
  %hs : {M3.sc.top(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(_)), M3.SOut{M3.LVal{}, db}, M3.SBad{})) == False{} : Bool}
  ls = Equal.sym(Bool, D1.lit_or_num(Lex.text(List.append(&2, Char, ba, [cc]))), False{}, lon_app(cc, hn, ba,
    tpt(D1.lit_or_num(Lex.text(ba)), da, ha)))
  %ls : {M3.sc.top(Bool.pick(M3.Sc, _, M3.SOut{M3.LVal{}, db}, M3.SBad{})) == False{} : Bool}
  {==}

# a scan related to one the scan accepts is not accepted
law acc_w:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +aa: M3.Sc
  for +bb: M3.Sc
  for h: rel_w(cc, aa, bb)
  for ha: {M3.sc.acc(aa) == True{} : Bool}
  {M3.sc.acc(bb) == False{} : Bool}

def acc_w(cc, hn, aa, bb, h, ha):
  match aa bb:
    case M3.SOut{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SOut{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, acc_w_ow(a1, a2, b1, b2, cc, h, ha))
    case M3.SOut{a1, a2} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SOut{a1, a2} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SOut{_a1, _a2} M3.SBad{}:
      {==}
    case M3.SWord{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SWord{a1, a2} M3.SWord{b1, b2}:
      acc_w_ww(cc, hn, a1, a2, b1, b2, h, ha)
    case M3.SWord{a1, a2} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SWord{a1, a2} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SWord{_a1, _a2} M3.SBad{}:
      {==}
    case M3.SIn{a1} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SIn{a1} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SIn{a1} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SIn{a1} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SIn{_a1} M3.SBad{}:
      {==}
    case M3.SEsc{a1} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SEsc{_a1} M3.SBad{}:
      {==}
    case M3.SBad{} M3.SOut{b1, b2}:
      M6.no({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SWord{b1, b2}:
      M6.no({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SIn{b1}:
      M6.no({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SEsc{b1}:
      M6.no({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SBad{}:
      M6.no({M3.sc.acc(M3.SBad{}) == False{} : Bool}, ha)

# a scan related to one the scan accepts is not accepted
law acc_q:
  for +aa: M3.Sc
  for +bb: M3.Sc
  for h: rel_q(aa, bb)
  for ha: {M3.sc.acc(aa) == True{} : Bool}
  {M3.sc.acc(bb) == False{} : Bool}

def acc_q(aa, bb, h, ha):
  match aa bb:
    case M3.SOut{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SOut{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SOut{a1, a2} M3.SIn{b1}:
      {==}
    case M3.SOut{a1, a2} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SOut{_a1, _a2} M3.SBad{}:
      {==}
    case M3.SWord{a1, a2} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SWord{a1, a2} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SWord{a1, a2} M3.SIn{b1}:
      {==}
    case M3.SWord{a1, a2} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SWord{_a1, _a2} M3.SBad{}:
      {==}
    case M3.SIn{a1} M3.SOut{b1, b2}:
      M6.no({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, ha)
    case M3.SIn{a1} M3.SWord{b1, b2}:
      M6.no({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, ha)
    case M3.SIn{a1} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SIn{a1} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SIn{_a1} M3.SBad{}:
      {==}
    case M3.SEsc{a1} M3.SOut{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SWord{b1, b2}:
      Empty.absurd({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SIn{b1}:
      Empty.absurd({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, h)
    case M3.SEsc{a1} M3.SEsc{b1}:
      Empty.absurd({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, h)
    case M3.SEsc{_a1} M3.SBad{}:
      {==}
    case M3.SBad{} M3.SOut{b1, b2}:
      M6.no({M3.sc.acc(M3.SOut{b1, b2}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SWord{b1, b2}:
      M6.no({M3.sc.acc(M3.SWord{b1, b2}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SIn{b1}:
      M6.no({M3.sc.acc(M3.SIn{b1}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SEsc{b1}:
      M6.no({M3.sc.acc(M3.SEsc{b1}) == False{} : Bool}, ha)
    case M3.SBad{} M3.SBad{}:
      M6.no({M3.sc.acc(M3.SBad{}) == False{} : Bool}, ha)

law io_o_arr:
  for +lt: M3.Lt
  for +dd: Nat
  for +cc: Char
  rel_o(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TOpenArr{}}, cc))

def io_o_arr(lt, _dd, _cc):
  match lt:
    case M3.LSt{}:
      ({==}, Unit{})
    case M3.LOp{}:
      ({==}, Unit{})
    case M3.LVal{}:
      Unit{}

law iw_o_arr:
  for +ba: List<&2, Char>
  for +dd: Nat
  for +cc: Char
  rel_o(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CPunct{Lex.TOpenArr{}}, cc))

def iw_o_arr(ba, dd, _cc):
  pick_r_o(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, dd}, M3.SBad{}, Unit{})

law init_o_arr:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +cc: Char
  rel_o(yy, M3.sc.stepc(yy, Lex.CPunct{Lex.TOpenArr{}}, cc))

def init_o_arr(yy, hb, cc):
  match yy:
    case M3.SOut{lt, dd}:
      io_o_arr(lt, dd, cc)
    case M3.SWord{ba, dd}:
      iw_o_arr(ba, dd, cc)
    case M3.SIn{dd}:
      Empty.absurd(rel_o(M3.SIn{dd}, M3.sc.stepc(M3.SIn{dd}, Lex.CPunct{Lex.TOpenArr{}}, cc)), hb)
    case M3.SEsc{dd}:
      Empty.absurd(rel_o(M3.SEsc{dd}, M3.sc.stepc(M3.SEsc{dd}, Lex.CPunct{Lex.TOpenArr{}}, cc)), hb)
    case M3.SBad{}:
      Unit{}

law cls_o_arr:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +post: String
  for ha: {M3.sc.acc(M3.sc.run(post, yy)) == True{} : Bool}
  for +cc: Char
  {M3.sc.acc(M3.sc.run(post, M3.sc.stepc(yy, Lex.CPunct{Lex.TOpenArr{}}, cc))) == False{} : Bool}

def cls_o_arr(yy, hb, post, ha, cc):
  acc_o(M3.sc.run(post, yy), M3.sc.run(post, M3.sc.stepc(yy, Lex.CPunct{Lex.TOpenArr{}}, cc)), run_o(post, yy,
      M3.sc.stepc(yy,
    Lex.CPunct{Lex.TOpenArr{}}, cc),
    init_o_arr(yy, hb, cc)), ha)

law io_o_obj:
  for +lt: M3.Lt
  for +dd: Nat
  for +cc: Char
  rel_o(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TOpenObj{}}, cc))

def io_o_obj(lt, _dd, _cc):
  match lt:
    case M3.LSt{}:
      ({==}, Unit{})
    case M3.LOp{}:
      ({==}, Unit{})
    case M3.LVal{}:
      Unit{}

law iw_o_obj:
  for +ba: List<&2, Char>
  for +dd: Nat
  for +cc: Char
  rel_o(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CPunct{Lex.TOpenObj{}}, cc))

def iw_o_obj(ba, dd, _cc):
  pick_r_o(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, dd}, M3.SBad{}, Unit{})

law init_o_obj:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +cc: Char
  rel_o(yy, M3.sc.stepc(yy, Lex.CPunct{Lex.TOpenObj{}}, cc))

def init_o_obj(yy, hb, cc):
  match yy:
    case M3.SOut{lt, dd}:
      io_o_obj(lt, dd, cc)
    case M3.SWord{ba, dd}:
      iw_o_obj(ba, dd, cc)
    case M3.SIn{dd}:
      Empty.absurd(rel_o(M3.SIn{dd}, M3.sc.stepc(M3.SIn{dd}, Lex.CPunct{Lex.TOpenObj{}}, cc)), hb)
    case M3.SEsc{dd}:
      Empty.absurd(rel_o(M3.SEsc{dd}, M3.sc.stepc(M3.SEsc{dd}, Lex.CPunct{Lex.TOpenObj{}}, cc)), hb)
    case M3.SBad{}:
      Unit{}

law cls_o_obj:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +post: String
  for ha: {M3.sc.acc(M3.sc.run(post, yy)) == True{} : Bool}
  for +cc: Char
  {M3.sc.acc(M3.sc.run(post, M3.sc.stepc(yy, Lex.CPunct{Lex.TOpenObj{}}, cc))) == False{} : Bool}

def cls_o_obj(yy, hb, post, ha, cc):
  acc_o(M3.sc.run(post, yy), M3.sc.run(post, M3.sc.stepc(yy, Lex.CPunct{Lex.TOpenObj{}}, cc)), run_o(post, yy,
      M3.sc.stepc(yy,
    Lex.CPunct{Lex.TOpenObj{}}, cc),
    init_o_obj(yy, hb, cc)), ha)

law io_c_arr:
  for +lt: M3.Lt
  for +dd: Nat
  for +cc: Char
  rel_c(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TCloseArr{}}, cc))

def io_c_arr(lt, dd, _cc):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      match dd:
        case 0n:
          Unit{}
        case 1n+n0:
          ({==}, Unit{})
    case M3.LVal{}:
      match dd:
        case 0n:
          Unit{}
        case 1n+n0:
          ({==}, Unit{})

law iw_c_arr:
  for +ba: List<&2, Char>
  for +dd: Nat
  for +cc: Char
  rel_c(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CPunct{Lex.TCloseArr{}}, cc))

def iw_c_arr(ba, dd, _cc):
  match dd:
    case 0n:
      pick_r_c(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, 0n}, M3.SBad{}, Unit{})
    case 1n+n0:
      pick_r_c(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, 1n+n0}, M3.SOut{M3.LVal{}, n0}, ({==}, Unit{}))

law init_c_arr:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +cc: Char
  rel_c(yy, M3.sc.stepc(yy, Lex.CPunct{Lex.TCloseArr{}}, cc))

def init_c_arr(yy, hb, cc):
  match yy:
    case M3.SOut{lt, dd}:
      io_c_arr(lt, dd, cc)
    case M3.SWord{ba, dd}:
      iw_c_arr(ba, dd, cc)
    case M3.SIn{dd}:
      Empty.absurd(rel_c(M3.SIn{dd}, M3.sc.stepc(M3.SIn{dd}, Lex.CPunct{Lex.TCloseArr{}}, cc)), hb)
    case M3.SEsc{dd}:
      Empty.absurd(rel_c(M3.SEsc{dd}, M3.sc.stepc(M3.SEsc{dd}, Lex.CPunct{Lex.TCloseArr{}}, cc)), hb)
    case M3.SBad{}:
      Unit{}

law cls_c_arr:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +post: String
  for ha: {M3.sc.acc(M3.sc.run(post, yy)) == True{} : Bool}
  for +cc: Char
  {M3.sc.acc(M3.sc.run(post, M3.sc.stepc(yy, Lex.CPunct{Lex.TCloseArr{}}, cc))) == False{} : Bool}

def cls_c_arr(yy, hb, post, ha, cc):
  acc_c(M3.sc.run(post, yy), M3.sc.run(post, M3.sc.stepc(yy, Lex.CPunct{Lex.TCloseArr{}}, cc)), run_c(post, yy,
      M3.sc.stepc(yy,
    Lex.CPunct{Lex.TCloseArr{}}, cc),
    init_c_arr(yy, hb, cc)), ha)

law io_c_obj:
  for +lt: M3.Lt
  for +dd: Nat
  for +cc: Char
  rel_c(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TCloseObj{}}, cc))

def io_c_obj(lt, dd, _cc):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      match dd:
        case 0n:
          Unit{}
        case 1n+n0:
          ({==}, Unit{})
    case M3.LVal{}:
      match dd:
        case 0n:
          Unit{}
        case 1n+n0:
          ({==}, Unit{})

law iw_c_obj:
  for +ba: List<&2, Char>
  for +dd: Nat
  for +cc: Char
  rel_c(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CPunct{Lex.TCloseObj{}}, cc))

def iw_c_obj(ba, dd, _cc):
  match dd:
    case 0n:
      pick_r_c(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, 0n}, M3.SBad{}, Unit{})
    case 1n+n0:
      pick_r_c(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, 1n+n0}, M3.SOut{M3.LVal{}, n0}, ({==}, Unit{}))

law init_c_obj:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +cc: Char
  rel_c(yy, M3.sc.stepc(yy, Lex.CPunct{Lex.TCloseObj{}}, cc))

def init_c_obj(yy, hb, cc):
  match yy:
    case M3.SOut{lt, dd}:
      io_c_obj(lt, dd, cc)
    case M3.SWord{ba, dd}:
      iw_c_obj(ba, dd, cc)
    case M3.SIn{dd}:
      Empty.absurd(rel_c(M3.SIn{dd}, M3.sc.stepc(M3.SIn{dd}, Lex.CPunct{Lex.TCloseObj{}}, cc)), hb)
    case M3.SEsc{dd}:
      Empty.absurd(rel_c(M3.SEsc{dd}, M3.sc.stepc(M3.SEsc{dd}, Lex.CPunct{Lex.TCloseObj{}}, cc)), hb)
    case M3.SBad{}:
      Unit{}

law cls_c_obj:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +post: String
  for ha: {M3.sc.acc(M3.sc.run(post, yy)) == True{} : Bool}
  for +cc: Char
  {M3.sc.acc(M3.sc.run(post, M3.sc.stepc(yy, Lex.CPunct{Lex.TCloseObj{}}, cc))) == False{} : Bool}

def cls_c_obj(yy, hb, post, ha, cc):
  acc_c(M3.sc.run(post, yy), M3.sc.run(post, M3.sc.stepc(yy, Lex.CPunct{Lex.TCloseObj{}}, cc)), run_c(post, yy,
      M3.sc.stepc(yy,
    Lex.CPunct{Lex.TCloseObj{}}, cc),
    init_c_obj(yy, hb, cc)), ha)

law io_q:
  for +lt: M3.Lt
  for +dd: Nat
  for +cc: Char
  rel_q(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CQuote{}, cc))

def io_q(lt, _dd, _cc):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law iw_q:
  for +ba: List<&2, Char>
  for +dd: Nat
  for +cc: Char
  rel_q(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CQuote{}, cc))

def iw_q(ba, dd, _cc):
  pick_r_q(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, dd}, M3.SBad{}, Unit{})

law init_q:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +cc: Char
  rel_q(yy, M3.sc.stepc(yy, Lex.CQuote{}, cc))

def init_q(yy, hb, cc):
  match yy:
    case M3.SOut{lt, dd}:
      io_q(lt, dd, cc)
    case M3.SWord{ba, dd}:
      iw_q(ba, dd, cc)
    case M3.SIn{dd}:
      Empty.absurd(rel_q(M3.SIn{dd}, M3.sc.stepc(M3.SIn{dd}, Lex.CQuote{}, cc)), hb)
    case M3.SEsc{dd}:
      Empty.absurd(rel_q(M3.SEsc{dd}, M3.sc.stepc(M3.SEsc{dd}, Lex.CQuote{}, cc)), hb)
    case M3.SBad{}:
      Unit{}

law cls_q:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +post: String
  for ha: {M3.sc.acc(M3.sc.run(post, yy)) == True{} : Bool}
  for +cc: Char
  {M3.sc.acc(M3.sc.run(post, M3.sc.stepc(yy, Lex.CQuote{}, cc))) == False{} : Bool}

def cls_q(yy, hb, post, ha, cc):
  acc_q(M3.sc.run(post, yy), M3.sc.run(post, M3.sc.stepc(yy, Lex.CQuote{}, cc)), run_q(post, yy, M3.sc.stepc(yy,
      Lex.CQuote{}, cc),
    init_q(yy, hb, cc)), ha)

# laws/WhitespaceBetweenTokensIgnored.bend: the scan for places between tokens against the character
# classes the scan of texts reads

# classify, its twelve tests named
def clb(
  b91: Bool,
  b93: Bool,
  b123: Bool,
  b125: Bool,
  b58: Bool,
  b44: Bool,
  b34: Bool,
  b92: Bool,
  b32: Bool,
  b10: Bool,
  b13: Bool,
  b9: Bool
) -> Lex.Class:
  Bool.pick(Lex.Class, b91, Lex.CPunct{Lex.TOpenArr{}}, Bool.pick(Lex.Class, b93, Lex.CPunct{Lex.TCloseArr{}},
    Bool.pick(Lex.Class, b123, Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, b125, Lex.CPunct{Lex.TCloseObj{}},
    Bool.pick(Lex.Class, b58, Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, b44, Lex.CPunct{Lex.TComma{}},
    Bool.pick(Lex.Class, b34, Lex.CQuote{}, Bool.pick(Lex.Class, b92, Lex.CBack{}, Bool.pick(Lex.Class, b32,
    Lex.CSpace{}, Bool.pick(Lex.Class, b10, Lex.CSpace{}, Bool.pick(Lex.Class, b13, Lex.CSpace{}, Bool.pick(Lex.Class,
    b9, Lex.CSpace{}, Lex.COther{}))))))))))))

# word_char, the same tests named
def wcb(
  b91: Bool,
  b93: Bool,
  b123: Bool,
  b125: Bool,
  b58: Bool,
  b44: Bool,
  b34: Bool,
  b92: Bool,
  b32: Bool,
  b10: Bool,
  b13: Bool,
  b9: Bool
) -> Bool:
  Bool.not(Bool.or(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13))), Bool.or(b91, Bool.or(b93, Bool.or(b123, Bool.or(b125,
    Bool.or(b58, Bool.or(b44, Bool.or(b34, b92)))))))))

# a word character is one classify calls one
law cwb:
  for +b91: Bool
  for +b93: Bool
  for +b123: Bool
  for +b125: Bool
  for +b58: Bool
  for +b44: Bool
  for +b34: Bool
  for +b92: Bool
  for +b32: Bool
  for +b10: Bool
  for +b13: Bool
  for +b9: Bool
  {wcb(b91, b93, b123, b125, b58, b44, b34, b92, b32, b10, b13, b9) == M3.is_oth(clb(b91, b93, b123, b125, b58, b44,
      b34,
    b92, b32, b10, b13, b9)) : Bool}

def cwb(b91, b93, b123, b125, b58, b44, b34, b92, b32, b10, b13, b9):
  match b91:
    case True{}:
      Equal.cong(Bool, Bool, zz => Bool.not(zz), Bool.or(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13))), True{}), True{},
        M5.or_true_r(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13)))))
    case False{}:
      match b93:
        case True{}:
          Equal.cong(Bool, Bool, zz => Bool.not(zz), Bool.or(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13))), True{}),
            True{}, M5.or_true_r(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13)))))
        case False{}:
          match b123:
            case True{}:
              Equal.cong(Bool, Bool, zz => Bool.not(zz), Bool.or(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13))), True{}),
                True{}, M5.or_true_r(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13)))))
            case False{}:
              match b125:
                case True{}:
                  Equal.cong(Bool, Bool, zz => Bool.not(zz), Bool.or(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13))),
                    True{}), True{}, M5.or_true_r(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13)))))
                case False{}:
                  match b58:
                    case True{}:
                      Equal.cong(Bool, Bool, zz => Bool.not(zz), Bool.or(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13))),
                        True{}), True{}, M5.or_true_r(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13)))))
                    case False{}:
                      match b44:
                        case True{}:
                          Equal.cong(Bool, Bool, zz => Bool.not(zz), Bool.or(Bool.or(b32, Bool.or(b9, Bool.or(b10,
                            b13))), True{}), True{}, M5.or_true_r(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13)))))
                        case False{}:
                          match b34:
                            case True{}:
                              Equal.cong(Bool, Bool, zz => Bool.not(zz), Bool.or(Bool.or(b32, Bool.or(b9, Bool.or(b10,
                                b13))), True{}), True{}, M5.or_true_r(Bool.or(b32, Bool.or(b9, Bool.or(b10, b13)))))
                            case False{}:
                              match b92:
                                case True{}:
                                  Equal.cong(Bool, Bool, zz => Bool.not(zz), Bool.or(Bool.or(b32, Bool.or(b9,
                                    Bool.or(b10, b13))), True{}), True{}, M5.or_true_r(Bool.or(b32, Bool.or(b9,
                                    Bool.or(b10, b13)))))
                                case False{}:
                                  match b32:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      match b10:
                                        case True{}:
                                          Equal.cong(Bool, Bool, zz => Bool.not(Bool.or(zz, Bool.or(False{},
                                            Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, Bool.or(False{},
                                            Bool.or(False{}, Bool.or(False{}, False{}))))))))), Bool.or(b9, True{}),
                                            True{}, M5.or_true_r(b9))
                                        case False{}:
                                          match b13:
                                            case True{}:
                                              Equal.cong(Bool, Bool, zz => Bool.not(Bool.or(zz, Bool.or(False{},
                                                Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, Bool.or(False{},
                                                Bool.or(False{}, Bool.or(False{}, False{}))))))))), Bool.or(b9,
                                                True{}), True{}, M5.or_true_r(b9))
                                            case False{}:
                                              match b9:
                                                case True{}:
                                                  {==}
                                                case False{}:
                                                  {==}

# word_char and classify agree
law cw:
  for +ch: Char
  {D1.word_char(ch) == M3.is_oth(Lex.classify(ch)) : Bool}

def cw(ch):
  match ch:
    case Chr{+uu}:
      cwb(U32.is_eq(uu, 91), U32.is_eq(uu, 93), U32.is_eq(uu, 123), U32.is_eq(uu, 125), U32.is_eq(uu, 58),
        U32.is_eq(uu, 44), U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_eq(uu, 32), U32.is_eq(uu, 10), U32.is_eq(uu,
        13), U32.is_eq(uu, 9))

# the gap scan, a character's class given
def gps(gg: Laws.Gp, +cls: Lex.Class) -> Laws.Gp:
  match gg:
    case Laws.GpOut{_}:
      Bool.pick(Laws.Gp, M2.is_quote(cls), Laws.GpIn{}, Laws.GpOut{M3.is_oth(cls)})
    case Laws.GpIn{}:
      Bool.pick(Laws.Gp, M2.is_back(cls), Laws.GpEsc{}, Bool.pick(Laws.Gp, M2.is_quote(cls), Laws.GpOut{False{}},
        Laws.GpIn{}))
    case Laws.GpEsc{}:
      Laws.GpIn{}

# a word's end on the left
def wt(ww: Bool) -> Type:
  match ww:
    case True{}:
      Unit
    case False{}:
      Empty

# what the two scans have in common: outside strings, in a word only after a
# word character, in a string, after a backslash in one; or a fault
def cpt(st: M3.Sc, gg: Laws.Gp) -> Type:
  match st:
    case M3.SOut{_, _}:
      match gg:
        case Laws.GpOut{_}:
          Unit
        case _:
          Empty
    case M3.SWord{_, _}:
      match gg:
        case Laws.GpOut{ww}:
          wt(ww)
        case _:
          Empty
    case M3.SIn{_}:
      match gg:
        case Laws.GpIn{}:
          Unit
        case _:
          Empty
    case M3.SEsc{_}:
      match gg:
        case Laws.GpEsc{}:
          Unit
        case _:
          Empty
    case M3.SBad{}:
      Unit

law pick_cp:
  for bv: Bool
  for +xx: M3.Sc
  for +gg: Laws.Gp
  for h: cpt(xx, gg)
  cpt(Bool.pick(M3.Sc, bv, xx, M3.SBad{}), gg)

def pick_cp(bv, _xx, _gg, h):
  match bv:
    case True{}:
      h
    case False{}:
      Unit{}

law cpo.c1:
  for +lt: M3.Lt
  for +dd: Nat
  for +ww: Bool
  for +ch: Char
  cpt(M3.sc.out(lt, dd, Lex.CPunct{Lex.TOpenArr{}}, ch), gps(Laws.GpOut{ww}, Lex.CPunct{Lex.TOpenArr{}}))

def cpo.c1(lt, _dd, _ww, _ch):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cpo.c2:
  for +lt: M3.Lt
  for +dd: Nat
  for +ww: Bool
  for +ch: Char
  cpt(M3.sc.out(lt, dd, Lex.CPunct{Lex.TCloseArr{}}, ch), gps(Laws.GpOut{ww}, Lex.CPunct{Lex.TCloseArr{}}))

def cpo.c2(lt, dd, _ww, _ch):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      match dd:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}
    case M3.LVal{}:
      match dd:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}

law cpo.c3:
  for +lt: M3.Lt
  for +dd: Nat
  for +ww: Bool
  for +ch: Char
  cpt(M3.sc.out(lt, dd, Lex.CPunct{Lex.TOpenObj{}}, ch), gps(Laws.GpOut{ww}, Lex.CPunct{Lex.TOpenObj{}}))

def cpo.c3(lt, _dd, _ww, _ch):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cpo.c4:
  for +lt: M3.Lt
  for +dd: Nat
  for +ww: Bool
  for +ch: Char
  cpt(M3.sc.out(lt, dd, Lex.CPunct{Lex.TCloseObj{}}, ch), gps(Laws.GpOut{ww}, Lex.CPunct{Lex.TCloseObj{}}))

def cpo.c4(lt, dd, _ww, _ch):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      match dd:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}
    case M3.LVal{}:
      match dd:
        case 0n:
          Unit{}
        case 1n+n0:
          Unit{}

law cpo.c5:
  for +lt: M3.Lt
  for +dd: Nat
  for +ww: Bool
  for +ch: Char
  cpt(M3.sc.out(lt, dd, Lex.CPunct{Lex.TColon{}}, ch), gps(Laws.GpOut{ww}, Lex.CPunct{Lex.TColon{}}))

def cpo.c5(lt, _dd, _ww, _ch):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cpo.c6:
  for +lt: M3.Lt
  for +dd: Nat
  for +ww: Bool
  for +ch: Char
  cpt(M3.sc.out(lt, dd, Lex.CPunct{Lex.TComma{}}, ch), gps(Laws.GpOut{ww}, Lex.CPunct{Lex.TComma{}}))

def cpo.c6(lt, _dd, _ww, _ch):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cpo.c7:
  for +lt: M3.Lt
  for +dd: Nat
  for +ww: Bool
  for +ch: Char
  cpt(M3.sc.out(lt, dd, Lex.CQuote{}, ch), gps(Laws.GpOut{ww}, Lex.CQuote{}))

def cpo.c7(lt, _dd, _ww, _ch):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cpo.c8:
  for +lt: M3.Lt
  for +dd: Nat
  for +ww: Bool
  for +ch: Char
  cpt(M3.sc.out(lt, dd, Lex.COther{}, ch), gps(Laws.GpOut{ww}, Lex.COther{}))

def cpo.c8(lt, _dd, _ww, _ch):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cpo:
  for +lt: M3.Lt
  for +dd: Nat
  for +ww: Bool
  for +cls: Lex.Class
  for +ch: Char
  cpt(M3.sc.out(lt, dd, cls, ch), gps(Laws.GpOut{ww}, cls))

def cpo(lt, dd, ww, cls, ch):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          cpo.c1(lt, dd, ww, ch)
        case Lex.TCloseArr{}:
          cpo.c2(lt, dd, ww, ch)
        case Lex.TOpenObj{}:
          cpo.c3(lt, dd, ww, ch)
        case Lex.TCloseObj{}:
          cpo.c4(lt, dd, ww, ch)
        case Lex.TColon{}:
          cpo.c5(lt, dd, ww, ch)
        case Lex.TComma{}:
          cpo.c6(lt, dd, ww, ch)
        case Lex.TStr{_x0}:
          Unit{}
        case Lex.TWord{_x0}:
          Unit{}
        case Lex.TStrS{_x0, _x1}:
          Unit{}
        case Lex.TWordS{_x0, _x1}:
          Unit{}
        case Lex.TBad{}:
          Unit{}
    case Lex.CQuote{}:
      cpo.c7(lt, dd, ww, ch)
    case Lex.CBack{}:
      Unit{}
    case Lex.CSpace{}:
      Unit{}
    case Lex.COther{}:
      cpo.c8(lt, dd, ww, ch)

law cpw.t.c1:
  for +dd: Nat
  for +ba: List<&2, Char>
  for +ch: Char
  cpt(M3.sc.word(ba, dd, Lex.CPunct{Lex.TCloseArr{}}, ch), gps(Laws.GpOut{True{}}, Lex.CPunct{Lex.TCloseArr{}}))

def cpw.t.c1(dd, ba, _ch):
  match dd:
    case 0n:
      pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, Laws.GpOut{False{}}, Unit{})
    case 1n+n0:
      pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, n0}, Laws.GpOut{False{}}, Unit{})

law cpw.t.c2:
  for +dd: Nat
  for +ba: List<&2, Char>
  for +ch: Char
  cpt(M3.sc.word(ba, dd, Lex.CPunct{Lex.TCloseObj{}}, ch), gps(Laws.GpOut{True{}}, Lex.CPunct{Lex.TCloseObj{}}))

def cpw.t.c2(dd, ba, _ch):
  match dd:
    case 0n:
      pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, Laws.GpOut{False{}}, Unit{})
    case 1n+n0:
      pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, n0}, Laws.GpOut{False{}}, Unit{})

law cpw.t:
  for +ba: List<&2, Char>
  for +dd: Nat
  for +cls: Lex.Class
  for +ch: Char
  cpt(M3.sc.word(ba, dd, cls, ch), gps(Laws.GpOut{True{}}, cls))

def cpw.t(ba, dd, cls, ch):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, Laws.GpOut{False{}}, Unit{})
        case Lex.TCloseArr{}:
          cpw.t.c1(dd, ba, ch)
        case Lex.TOpenObj{}:
          pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, Laws.GpOut{False{}}, Unit{})
        case Lex.TCloseObj{}:
          cpw.t.c2(dd, ba, ch)
        case Lex.TColon{}:
          pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, dd}, Laws.GpOut{False{}}, Unit{})
        case Lex.TComma{}:
          pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, dd}, Laws.GpOut{False{}}, Unit{})
        case Lex.TStr{_x0}:
          pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, Laws.GpOut{False{}}, Unit{})
        case Lex.TWord{_x0}:
          pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, Laws.GpOut{False{}}, Unit{})
        case Lex.TStrS{_x0, _x1}:
          pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, Laws.GpOut{False{}}, Unit{})
        case Lex.TWordS{_x0, _x1}:
          pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, Laws.GpOut{False{}}, Unit{})
        case Lex.TBad{}:
          pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, Laws.GpOut{False{}}, Unit{})
    case Lex.CQuote{}:
      pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, Laws.GpIn{}, Unit{})
    case Lex.CBack{}:
      pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SBad{}, Laws.GpOut{False{}}, Unit{})
    case Lex.CSpace{}:
      pick_cp(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LVal{}, dd}, Laws.GpOut{False{}}, Unit{})
    case Lex.COther{}:
      Unit{}

law cpi:
  for +dd: Nat
  for +cls: Lex.Class
  cpt(M3.sc.in(dd, cls), gps(Laws.GpIn{}, cls))

def cpi(_dd, cls):
  match cls:
    case Lex.CPunct{tk}:
      Unit{}
    case Lex.CQuote{}:
      Unit{}
    case Lex.CBack{}:
      Unit{}
    case Lex.CSpace{}:
      Unit{}
    case Lex.COther{}:
      Unit{}

# is_cp 92 is classify's reverse solidus
law cb.at:
  for +uu: U32
  for cls: Lex.Class
  for e: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  {U32.is_eq(uu, 92) == M2.is_back(cls) : Bool}

def cb.at(uu, cls, e):
  match cls:
    case Lex.CPunct{+tk}:
      M5.nb(U32.is_eq(uu, 92), uu, Lex.CPunct{tk}, {==}, e, {==})
    case Lex.CQuote{}:
      M5.nb(U32.is_eq(uu, 92), uu, Lex.CQuote{}, {==}, e, {==})
    case Lex.CBack{}:
      Equal.cong(U32, Bool, zz => U32.is_eq(zz, 92), uu, 92, M2.cls_back(Chr{uu}, e))
    case Lex.CSpace{}:
      M5.nb(U32.is_eq(uu, 92), uu, Lex.CSpace{}, {==}, e, {==})
    case Lex.COther{}:
      M5.nb(U32.is_eq(uu, 92), uu, Lex.COther{}, {==}, e, {==})

law cb:
  for +ch: Char
  {D1.is_cp(ch, 92) == M2.is_back(Lex.classify(ch)) : Bool}

def cb(ch):
  match ch:
    case Chr{+uu}:
      cb.at(uu, Lex.classify(Chr{uu}), {==})

# the gap scan's step reads only the character's class
law gp_eq:
  for +gg: Laws.Gp
  for +ch: Char
  {Laws.gp.step(gg, ch) == gps(gg, Lex.classify(ch)) : Laws.Gp}

def gp_eq(gg, ch):
  match gg:
    case Laws.GpOut{_ww}:
      e1 = M7.cq(ch)
      %e1 : {Bool.pick(Laws.Gp, D1.is_cp(ch, 34), Laws.GpIn{}, Laws.GpOut{D1.word_char(ch)}) == Bool.pick(Laws.Gp,
        _,
        Laws.GpIn{}, Laws.GpOut{M3.is_oth(Lex.classify(ch))}) : Laws.Gp}
      e2 = cw(ch)
      %e2 : {Bool.pick(Laws.Gp, D1.is_cp(ch, 34), Laws.GpIn{}, Laws.GpOut{D1.word_char(ch)}) == Bool.pick(Laws.Gp,
        D1.is_cp(ch, 34), Laws.GpIn{}, Laws.GpOut{_}) : Laws.Gp}
      {==}
    case Laws.GpIn{}:
      e1 = cb(ch)
      %e1 : {Bool.pick(Laws.Gp, D1.is_cp(ch, 92), Laws.GpEsc{}, Bool.pick(Laws.Gp, D1.is_cp(ch, 34),
        Laws.GpOut{False{}},
        Laws.GpIn{})) == Bool.pick(Laws.Gp, _, Laws.GpEsc{}, Bool.pick(Laws.Gp, M2.is_quote(Lex.classify(ch)),
        Laws.GpOut{False{}}, Laws.GpIn{})) : Laws.Gp}
      e2 = M7.cq(ch)
      %e2 : {Bool.pick(Laws.Gp, D1.is_cp(ch, 92), Laws.GpEsc{}, Bool.pick(Laws.Gp, D1.is_cp(ch, 34),
        Laws.GpOut{False{}},
        Laws.GpIn{})) == Bool.pick(Laws.Gp, D1.is_cp(ch, 92), Laws.GpEsc{}, Bool.pick(Laws.Gp, _, Laws.GpOut{False{}},
        Laws.GpIn{})) : Laws.Gp}
      {==}
    case Laws.GpEsc{}:
      {==}

# a word on the left needs a word character before it
law cpw:
  for +ww: Bool
  for +ba: List<&2, Char>
  for +dd: Nat
  for +cls: Lex.Class
  for +ch: Char
  for h: wt(ww)
  cpt(M3.sc.word(ba, dd, cls, ch), gps(Laws.GpOut{ww}, cls))

def cpw(ww, ba, dd, cls, ch, h):
  match ww:
    case True{}:
      cpw.t(ba, dd, cls, ch)
    case False{}:
      Empty.absurd(cpt(M3.sc.word(ba, dd, cls, ch), gps(Laws.GpOut{False{}}, cls)), h)

# one character keeps the two scans agreeing
law cps:
  for +st: M3.Sc
  for +gg: Laws.Gp
  for +cls: Lex.Class
  for +ch: Char
  for h: cpt(st, gg)
  cpt(M3.sc.stepc(st, cls, ch), gps(gg, cls))

def cps(st, gg, cls, ch, h):
  match st gg:
    case M3.SOut{lt, dd} Laws.GpOut{ww}:
      cpo(lt, dd, ww, cls, ch)
    case M3.SOut{lt, dd} Laws.GpIn{}:
      Empty.absurd(cpt(M3.sc.stepc(M3.SOut{lt, dd}, cls, ch), gps(Laws.GpIn{}, cls)), h)
    case M3.SOut{lt, dd} Laws.GpEsc{}:
      Empty.absurd(cpt(M3.sc.stepc(M3.SOut{lt, dd}, cls, ch), gps(Laws.GpEsc{}, cls)), h)
    case M3.SWord{ba, dd} Laws.GpOut{ww}:
      cpw(ww, ba, dd, cls, ch, h)
    case M3.SWord{ba, dd} Laws.GpIn{}:
      Empty.absurd(cpt(M3.sc.stepc(M3.SWord{ba, dd}, cls, ch), gps(Laws.GpIn{}, cls)), h)
    case M3.SWord{ba, dd} Laws.GpEsc{}:
      Empty.absurd(cpt(M3.sc.stepc(M3.SWord{ba, dd}, cls, ch), gps(Laws.GpEsc{}, cls)), h)
    case M3.SIn{dd} Laws.GpOut{ww}:
      Empty.absurd(cpt(M3.sc.stepc(M3.SIn{dd}, cls, ch), gps(Laws.GpOut{ww}, cls)), h)
    case M3.SIn{dd} Laws.GpIn{}:
      cpi(dd, cls)
    case M3.SIn{dd} Laws.GpEsc{}:
      Empty.absurd(cpt(M3.sc.stepc(M3.SIn{dd}, cls, ch), gps(Laws.GpEsc{}, cls)), h)
    case M3.SEsc{dd} Laws.GpOut{ww}:
      Empty.absurd(cpt(M3.sc.stepc(M3.SEsc{dd}, cls, ch), gps(Laws.GpOut{ww}, cls)), h)
    case M3.SEsc{dd} Laws.GpIn{}:
      Empty.absurd(cpt(M3.sc.stepc(M3.SEsc{dd}, cls, ch), gps(Laws.GpIn{}, cls)), h)
    case M3.SEsc{_dd} Laws.GpEsc{}:
      Unit{}
    case M3.SBad{} _gg:
      Unit{}

law cp1:
  for +st: M3.Sc
  for +gg: Laws.Gp
  for +hd: Char
  for h: cpt(st, gg)
  cpt(M3.sc.step(st, hd), Laws.gp.step(gg, hd))

def cp1(st, gg, hd, h):
  ge = Equal.sym(Laws.Gp, Laws.gp.step(gg, hd), gps(gg, Lex.classify(hd)), gp_eq(gg, hd))
  %ge : cpt(M3.sc.step(st, hd), _)
  cps(st, gg, Lex.classify(hd), hd, h)

# the two scans agree over any text
law cp_run:
  for +txt: String
  for +st: M3.Sc
  for +gg: Laws.Gp
  for h: cpt(st, gg)
  cpt(M3.sc.run(txt, st), Laws.gp.run(txt, gg))

def cp_run(txt, st, gg, h):
  match txt:
    case SNil{}:
      h
    case SCon{+hd, +tl}:
      cp_run(tl, M3.sc.step(st, hd), Laws.gp.step(gg, hd), cp1(st, gg, hd, h))

# laws/WhitespaceBetweenTokensIgnored.bend: the classes of character put between tokens

# a word's end and a step, in either order
law pick_step2:
  for bv: Bool
  for +yy: M3.Sc
  for +cls: Lex.Class
  for +ch: Char
  {Bool.pick(M3.Sc, bv, M3.sc.stepc(yy, cls, ch), M3.SBad{}) == M3.sc.stepc(Bool.pick(M3.Sc, bv, yy, M3.SBad{}), cls,
      ch) : M3.Sc}

def pick_step2(bv, _yy, _cls, _ch):
  match bv:
    case True{}:
      {==}
    case False{}:
      {==}

# a separator right after a word, then no word character
law sep_w.k:
  for +ba: List<&2, Char>
  for +dd: Nat
  for +cls: Lex.Class
  for +ch: Char
  rel_s(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(ba)), M3.sc.out(M3.LVal{}, dd, cls, ch), M3.SBad{}),
    M3.sc.stepc(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, dd}, M3.SBad{}), cls, ch))

def sep_w.k(ba, dd, cls, ch):
  ps = pick_step2(D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, dd}, cls, ch)
  %ps : rel_s(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(ba)), M3.sc.out(M3.LVal{}, dd, cls, ch), M3.SBad{}), _)
  pick_lr_s(D1.lit_or_num(Lex.text(ba)), M3.sc.out(M3.LVal{}, dd, cls, ch), M3.sc.stepc(M3.SOut{M3.LSt{}, dd}, cls, ch),
    cl_s_oo.s(M3.LVal{}, dd, M3.LSt{}, dd, cls, ch, Unit{}))

law sep_w:
  for +ba: List<&2, Char>
  for +dd: Nat
  for +cls: Lex.Class
  for +ch: Char
  for hn: {M3.is_oth(cls) == False{} : Bool}
  rel_s(M3.sc.word(ba, dd, cls, ch), M3.sc.stepc(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, dd},
      M3.SBad{}), cls,
    ch))

def sep_w(ba, dd, cls, ch, hn):
  match cls:
    case Lex.CPunct{+tk}:
      sep_w.k(ba, dd, Lex.CPunct{tk}, ch)
    case Lex.CQuote{}:
      sep_w.k(ba, dd, Lex.CQuote{}, ch)
    case Lex.CBack{}:
      sep_w.k(ba, dd, Lex.CBack{}, ch)
    case Lex.CSpace{}:
      sep_w.k(ba, dd, Lex.CSpace{}, ch)
    case Lex.COther{}:
      Empty.absurd(rel_s(M3.sc.word(ba, dd, Lex.COther{}, ch), M3.sc.stepc(Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(ba)),
        M3.SOut{M3.LSt{}, dd}, M3.SBad{}), Lex.COther{}, ch)), M1.true_false(hn))

# a separator right after a word
law sep_word:
  for +ba: List<&2, Char>
  for +dd: Nat
  for +post: String
  for hg: gw(post)
  for ha: {M3.sc.acc(M3.sc.run(post, M3.SWord{ba, dd})) == True{} : Bool}
  {M3.sc.acc(M3.sc.run(post, Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, dd},
      M3.SBad{}))) == False{} : Bool}

def sep_word(ba, dd, post, hg, ha):
  match post:
    case SNil{}:
      acc_pst(D1.lit_or_num(Lex.text(ba)), dd)
    case SCon{+hd, +tl}:
      +bb = Bool.pick(M3.Sc, D1.lit_or_num(Lex.text(ba)), M3.SOut{M3.LSt{}, dd}, M3.SBad{})
      acc_s(M3.sc.run(tl, M3.sc.step(M3.SWord{ba, dd}, hd)), M3.sc.run(tl, M3.sc.step(bb, hd)), run_s(tl,
          M3.sc.step(M3.SWord{ba, dd}, hd),
        M3.sc.step(bb, hd), sep_w(ba, dd, Lex.classify(hd), hd, hg)), ha)

law io_s_col:
  for +lt: M3.Lt
  for +dd: Nat
  for +cc: Char
  rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TColon{}}, cc))

def io_s_col(lt, _dd, _cc):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cls_s_col:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +post: String
  for hg: gapw(yy, post)
  for ha: {M3.sc.acc(M3.sc.run(post, yy)) == True{} : Bool}
  for +cc: Char
  {M3.sc.acc(M3.sc.run(post, M3.sc.stepc(yy, Lex.CPunct{Lex.TColon{}}, cc))) == False{} : Bool}

def cls_s_col(yy, hb, post, hg, ha, cc):
  match yy:
    case M3.SOut{+lt, +dd}:
      acc_s(M3.sc.run(post, M3.SOut{lt, dd}), M3.sc.run(post, M3.sc.out(lt, dd, Lex.CPunct{Lex.TColon{}}, cc)),
          run_s(post,
        M3.SOut{lt, dd}, M3.sc.out(lt, dd,
        Lex.CPunct{Lex.TColon{}}, cc), io_s_col(lt, dd, cc)), ha)
    case M3.SWord{+ba, +dd}:
      sep_word(ba, dd, post, hg, ha)
    case M3.SIn{dd}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.stepc(M3.SIn{dd}, Lex.CPunct{Lex.TColon{}},
          cc))) == False{} : Bool}, hb)
    case M3.SEsc{dd}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.stepc(M3.SEsc{dd}, Lex.CPunct{Lex.TColon{}},
          cc))) == False{} : Bool}, hb)
    case M3.SBad{}:
      Equal.cong(M3.Sc, Bool, zz => M3.sc.acc(zz), M3.sc.run(post, M3.SBad{}), M3.SBad{}, sc_bad(post))

law io_s_com:
  for +lt: M3.Lt
  for +dd: Nat
  for +cc: Char
  rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TComma{}}, cc))

def io_s_com(lt, _dd, _cc):
  match lt:
    case M3.LSt{}:
      Unit{}
    case M3.LOp{}:
      Unit{}
    case M3.LVal{}:
      Unit{}

law cls_s_com:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +post: String
  for hg: gapw(yy, post)
  for ha: {M3.sc.acc(M3.sc.run(post, yy)) == True{} : Bool}
  for +cc: Char
  {M3.sc.acc(M3.sc.run(post, M3.sc.stepc(yy, Lex.CPunct{Lex.TComma{}}, cc))) == False{} : Bool}

def cls_s_com(yy, hb, post, hg, ha, cc):
  match yy:
    case M3.SOut{+lt, +dd}:
      acc_s(M3.sc.run(post, M3.SOut{lt, dd}), M3.sc.run(post, M3.sc.out(lt, dd, Lex.CPunct{Lex.TComma{}}, cc)),
          run_s(post,
        M3.SOut{lt, dd}, M3.sc.out(lt, dd,
        Lex.CPunct{Lex.TComma{}}, cc), io_s_com(lt, dd, cc)), ha)
    case M3.SWord{+ba, +dd}:
      sep_word(ba, dd, post, hg, ha)
    case M3.SIn{dd}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.stepc(M3.SIn{dd}, Lex.CPunct{Lex.TComma{}},
          cc))) == False{} : Bool}, hb)
    case M3.SEsc{dd}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.stepc(M3.SEsc{dd}, Lex.CPunct{Lex.TComma{}},
          cc))) == False{} : Bool}, hb)
    case M3.SBad{}:
      Equal.cong(M3.Sc, Bool, zz => M3.sc.acc(zz), M3.sc.run(post, M3.SBad{}), M3.SBad{}, sc_bad(post))

# a word character where a value may come
law iw0:
  for +cc: Char
  for +lt: M3.Lt
  for +dd: Nat
  rel_w(cc, M3.SOut{lt, dd}, M3.sc.wstart(lt, dd, cc))

def iw0(_cc, lt, _dd):
  match lt:
    case M3.LSt{}:
      (Unit{}, {==})
    case M3.LOp{}:
      (Unit{}, {==})
    case M3.LVal{}:
      Unit{}

# a word character right after a word, then no word character
law ww1:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +ba: List<&2, Char>
  for +dd: Nat
  for +cls: Lex.Class
  for +ch: Char
  for hc: {M3.is_oth(cls) == False{} : Bool}
  rel_w(cc, M3.sc.word(ba, dd, cls, ch), M3.sc.word(cc <> ba, dd, cls, ch))

def ww1(cc, hn, ba, dd, cls, ch, hc):
  match cls:
    case Lex.CPunct{+tk}:
      pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(cc <> ba)), M3.sc.out(M3.LVal{}, dd,
          Lex.CPunct{tk},
        ch), M3.sc.out(M3.LVal{}, dd, Lex.CPunct{tk}, ch), ee => lon_cns(cc, hn, ba, ee))
    case Lex.CQuote{}:
      pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(cc <> ba)), M3.sc.out(M3.LVal{}, dd, Lex.CQuote{},
        ch), M3.sc.out(M3.LVal{}, dd, Lex.CQuote{}, ch), ee => lon_cns(cc, hn, ba, ee))
    case Lex.CBack{}:
      pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(cc <> ba)), M3.sc.out(M3.LVal{}, dd, Lex.CBack{},
        ch), M3.sc.out(M3.LVal{}, dd, Lex.CBack{}, ch), ee => lon_cns(cc, hn, ba, ee))
    case Lex.CSpace{}:
      pick2_w(cc, D1.lit_or_num(Lex.text(ba)), D1.lit_or_num(Lex.text(cc <> ba)), M3.sc.out(M3.LVal{}, dd, Lex.CSpace{},
        ch), M3.sc.out(M3.LVal{}, dd, Lex.CSpace{}, ch), ee => lon_cns(cc, hn, ba, ee))
    case Lex.COther{}:
      Empty.absurd(rel_w(cc, M3.sc.word(ba, dd, Lex.COther{}, ch), M3.sc.word(cc <> ba, dd, Lex.COther{}, ch)),
        M1.true_false(hc))

# a word character right after a word
law word_word:
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +ba: List<&2, Char>
  for +dd: Nat
  for +post: String
  for hg: gw(post)
  for ha: {M3.sc.acc(M3.sc.run(post, M3.SWord{ba, dd})) == True{} : Bool}
  {M3.sc.acc(M3.sc.run(post, M3.SWord{cc <> ba, dd})) == False{} : Bool}

def word_word(cc, hn, ba, dd, post, hg, ha):
  match post:
    case SNil{}:
      ls = Equal.sym(Bool, D1.lit_or_num(Lex.text(cc <> ba)), False{}, lon_cns(cc, hn, ba,
        tpt(D1.lit_or_num(Lex.text(ba)), dd, ha)))
      %ls : {M3.sc.top(Bool.pick(M3.Sc, _, M3.SOut{M3.LVal{}, dd}, M3.SBad{})) == False{} : Bool}
      {==}
    case SCon{+hd, +tl}:
      acc_w(cc, hn, M3.sc.run(tl, M3.sc.step(M3.SWord{ba, dd}, hd)), M3.sc.run(tl, M3.sc.step(M3.SWord{cc <> ba, dd},
          hd)), run_w(cc, hn,
        tl, M3.sc.step(M3.SWord{ba, dd}, hd), M3.sc.step(M3.SWord{cc <> ba, dd}, hd), ww1(cc, hn, ba, dd,
            Lex.classify(hd), hd,
          hg)),
        ha)

law cls_w:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +post: String
  for hg: gapw(yy, post)
  for ha: {M3.sc.acc(M3.sc.run(post, yy)) == True{} : Bool}
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  {M3.sc.acc(M3.sc.run(post, M3.sc.stepc(yy, Lex.COther{}, cc))) == False{} : Bool}

def cls_w(yy, hb, post, hg, ha, cc, hn):
  match yy:
    case M3.SOut{+lt, +dd}:
      acc_w(cc, hn, M3.sc.run(post, M3.SOut{lt, dd}), M3.sc.run(post, M3.sc.wstart(lt, dd, cc)), run_w(cc, hn, post,
          M3.SOut{lt, dd},
        M3.sc.wstart(lt, dd, cc), iw0(cc, lt, dd)), ha)
    case M3.SWord{+ba, +dd}:
      word_word(cc, hn, ba, dd, post, hg, ha)
    case M3.SIn{dd}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.stepc(M3.SIn{dd}, Lex.COther{}, cc))) == False{} : Bool}, hb)
    case M3.SEsc{dd}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.stepc(M3.SEsc{dd}, Lex.COther{}, cc))) == False{} : Bool}, hb)
    case M3.SBad{}:
      Equal.cong(M3.Sc, Bool, zz => M3.sc.acc(zz), M3.sc.run(post, M3.SBad{}), M3.SBad{}, sc_bad(post))

# a character the scan faults on outside strings
def tbad(tk: Lex.Tok) -> Bool:
  match tk:
    case Lex.TStr{_}:
      True{}
    case Lex.TWord{_}:
      True{}
    case Lex.TStrS{_, _}:
      True{}
    case Lex.TWordS{_, _}:
      True{}
    case Lex.TBad{}:
      True{}
    case _:
      False{}

def cbad(cls: Lex.Class) -> Bool:
  match cls:
    case Lex.CPunct{tk}:
      tbad(tk)
    case Lex.CBack{}:
      True{}
    case _:
      False{}

law ib_o:
  for +cls: Lex.Class
  for +cc: Char
  for +lt: M3.Lt
  for +dd: Nat
  for hbad: {cbad(cls) == True{} : Bool}
  rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, cls, cc))

def ib_o(cls, cc, lt, dd, hbad):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          M6.no(rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TOpenArr{}}, cc)), hbad)
        case Lex.TCloseArr{}:
          M6.no(rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TCloseArr{}}, cc)), hbad)
        case Lex.TOpenObj{}:
          M6.no(rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TOpenObj{}}, cc)), hbad)
        case Lex.TCloseObj{}:
          M6.no(rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TCloseObj{}}, cc)), hbad)
        case Lex.TColon{}:
          M6.no(rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TColon{}}, cc)), hbad)
        case Lex.TComma{}:
          M6.no(rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CPunct{Lex.TComma{}}, cc)), hbad)
        case Lex.TStr{_x0}:
          Unit{}
        case Lex.TWord{_x0}:
          Unit{}
        case Lex.TStrS{_x0, _x1}:
          Unit{}
        case Lex.TWordS{_x0, _x1}:
          Unit{}
        case Lex.TBad{}:
          Unit{}
    case Lex.CQuote{}:
      M6.no(rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CQuote{}, cc)), hbad)
    case Lex.CBack{}:
      Unit{}
    case Lex.CSpace{}:
      M6.no(rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.CSpace{}, cc)), hbad)
    case Lex.COther{}:
      M6.no(rel_s(M3.SOut{lt, dd}, M3.sc.out(lt, dd, Lex.COther{}, cc)), hbad)

law ib_w:
  for +cls: Lex.Class
  for +cc: Char
  for +ba: List<&2, Char>
  for +dd: Nat
  for hbad: {cbad(cls) == True{} : Bool}
  rel_s(M3.SWord{ba, dd}, M3.sc.word(ba, dd, cls, cc))

def ib_w(cls, cc, ba, dd, hbad):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          M6.no(rel_s(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CPunct{Lex.TOpenArr{}}, cc)), hbad)
        case Lex.TCloseArr{}:
          M6.no(rel_s(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CPunct{Lex.TCloseArr{}}, cc)), hbad)
        case Lex.TOpenObj{}:
          M6.no(rel_s(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CPunct{Lex.TOpenObj{}}, cc)), hbad)
        case Lex.TCloseObj{}:
          M6.no(rel_s(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CPunct{Lex.TCloseObj{}}, cc)), hbad)
        case Lex.TColon{}:
          M6.no(rel_s(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CPunct{Lex.TColon{}}, cc)), hbad)
        case Lex.TComma{}:
          M6.no(rel_s(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CPunct{Lex.TComma{}}, cc)), hbad)
        case Lex.TStr{_x0}:
          pick_r_s(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, dd}, M3.SBad{}, Unit{})
        case Lex.TWord{_x0}:
          pick_r_s(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, dd}, M3.SBad{}, Unit{})
        case Lex.TStrS{_x0, _x1}:
          pick_r_s(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, dd}, M3.SBad{}, Unit{})
        case Lex.TWordS{_x0, _x1}:
          pick_r_s(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, dd}, M3.SBad{}, Unit{})
        case Lex.TBad{}:
          pick_r_s(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, dd}, M3.SBad{}, Unit{})
    case Lex.CQuote{}:
      M6.no(rel_s(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CQuote{}, cc)), hbad)
    case Lex.CBack{}:
      pick_r_s(D1.lit_or_num(Lex.text(ba)), M3.SWord{ba, dd}, M3.SBad{}, Unit{})
    case Lex.CSpace{}:
      M6.no(rel_s(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.CSpace{}, cc)), hbad)
    case Lex.COther{}:
      M6.no(rel_s(M3.SWord{ba, dd}, M3.sc.word(ba, dd, Lex.COther{}, cc)), hbad)

law init_b:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +cls: Lex.Class
  for +cc: Char
  for +hbad: {cbad(cls) == True{} : Bool}
  rel_s(yy, M3.sc.stepc(yy, cls, cc))

def init_b(yy, hb, cls, cc, hbad):
  match yy:
    case M3.SOut{lt, dd}:
      ib_o(cls, cc, lt, dd, hbad)
    case M3.SWord{ba, dd}:
      ib_w(cls, cc, ba, dd, hbad)
    case M3.SIn{dd}:
      Empty.absurd(rel_s(M3.SIn{dd}, M3.sc.stepc(M3.SIn{dd}, cls, cc)), hb)
    case M3.SEsc{dd}:
      Empty.absurd(rel_s(M3.SEsc{dd}, M3.sc.stepc(M3.SEsc{dd}, cls, cc)), hb)
    case M3.SBad{}:
      Unit{}

law cls_b:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +post: String
  for ha: {M3.sc.acc(M3.sc.run(post, yy)) == True{} : Bool}
  for +cc: Char
  for +cls: Lex.Class
  for hbad: {cbad(cls) == True{} : Bool}
  {M3.sc.acc(M3.sc.run(post, M3.sc.stepc(yy, cls, cc))) == False{} : Bool}

def cls_b(yy, hb, post, ha, cc, cls, hbad):
  acc_s(M3.sc.run(post, yy), M3.sc.run(post, M3.sc.stepc(yy, cls, cc)), run_s(post, yy, M3.sc.stepc(yy, cls, cc),
      init_b(yy, hb,
    cls, cc, hbad)), ha)

# laws/WhitespaceBetweenTokensIgnored.bend: any character but whitespace, a digit or `-` put at a place
# between tokens: the scan without it accepts, with it it does not
law by_cls.at:
  for +yy: M3.Sc
  for hb: bnd(yy)
  for +post: String
  for hg: gapw(yy, post)
  for ha: {M3.sc.acc(M3.sc.run(post, yy)) == True{} : Bool}
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +hw: {D1.is_ws(cc) == False{} : Bool}
  for +cls: Lex.Class
  for +e: {Lex.classify(cc) == cls : Lex.Class}
  {M3.sc.acc(M3.sc.run(post, M3.sc.stepc(yy, cls, cc))) == False{} : Bool}

def by_cls.at(yy, hb, post, hg, ha, cc, hn, hw, cls, e):
  match cls:
    case Lex.CPunct{tk}:
      match tk:
        case Lex.TOpenArr{}:
          cls_o_arr(yy, hb, post, ha, cc)
        case Lex.TCloseArr{}:
          cls_c_arr(yy, hb, post, ha, cc)
        case Lex.TOpenObj{}:
          cls_o_obj(yy, hb, post, ha, cc)
        case Lex.TCloseObj{}:
          cls_c_obj(yy, hb, post, ha, cc)
        case Lex.TColon{}:
          cls_s_col(yy, hb, post, hg, ha, cc)
        case Lex.TComma{}:
          cls_s_com(yy, hb, post, hg, ha, cc)
        case Lex.TStr{x0}:
          cls_b(yy, hb, post, ha, cc, Lex.CPunct{Lex.TStr{x0}}, {==})
        case Lex.TWord{x0}:
          cls_b(yy, hb, post, ha, cc, Lex.CPunct{Lex.TWord{x0}}, {==})
        case Lex.TStrS{x0, x1}:
          cls_b(yy, hb, post, ha, cc, Lex.CPunct{Lex.TStrS{x0, x1}}, {==})
        case Lex.TWordS{x0, x1}:
          cls_b(yy, hb, post, ha, cc, Lex.CPunct{Lex.TWordS{x0, x1}}, {==})
        case Lex.TBad{}:
          cls_b(yy, hb, post, ha, cc, Lex.CPunct{Lex.TBad{}}, {==})
    case Lex.CQuote{}:
      cls_q(yy, hb, post, ha, cc)
    case Lex.CBack{}:
      cls_b(yy, hb, post, ha, cc, Lex.CBack{}, {==})
    case Lex.CSpace{}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.stepc(yy, Lex.CSpace{}, cc))) == False{} : Bool},
        M1.true_false(Equal.trans(Bool, True{}, D1.is_ws(cc), False{}, Equal.sym(Bool, D1.is_ws(cc), True{},
        M7.cls_space(cc, e)), hw)))
    case Lex.COther{}:
      cls_w(yy, hb, post, hg, ha, cc, hn)

# after a word, the text after the place starts with no word character
law gw_of:
  for +post: String
  for hg: {Laws.gap.at(Laws.GpOut{True{}}, post) == True{} : Bool}
  gw(post)

def gw_of(post, hg):
  match post:
    case SNil{}:
      Unit{}
    case SCon{+hd, _tl}:
      Equal.trans(Bool, M3.is_oth(Lex.classify(hd)), D1.word_char(hd), False{}, Equal.sym(Bool, D1.word_char(hd),
        M3.is_oth(Lex.classify(hd)), cw(hd)), M10.not_true(D1.word_char(hd), hg))

law ins_w:
  for +ww: Bool
  for +ba: List<&2, Char>
  for +dd: Nat
  for +post: String
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +hw: {D1.is_ws(cc) == False{} : Bool}
  for hc: wt(ww)
  for hg: {Laws.gap.at(Laws.GpOut{ww}, post) == True{} : Bool}
  for ha: {M3.sc.acc(M3.sc.run(post, M3.SWord{ba, dd})) == True{} : Bool}
  {M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SWord{ba, dd}, cc))) == False{} : Bool}

def ins_w(ww, ba, dd, post, cc, hn, hw, hc, hg, ha):
  match ww:
    case True{}:
      by_cls.at(M3.SWord{ba, dd}, Unit{}, post, gw_of(post, hg), ha, cc, hn, hw, Lex.classify(cc), {==})
    case False{}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SWord{ba, dd}, cc))) == False{} : Bool}, hc)

# the place after the scan of pre: a character put there makes the scan fail
law ins_at:
  for +yy: M3.Sc
  for +gg: Laws.Gp
  for +post: String
  for +cc: Char
  for +hn: {Bool.or(D2.digit(cc), D1.is_cp(cc, 45)) == False{} : Bool}
  for +hw: {D1.is_ws(cc) == False{} : Bool}
  for hc: cpt(yy, gg)
  for hg: {Laws.gap.at(gg, post) == True{} : Bool}
  for ha: {M3.sc.acc(M3.sc.run(post, yy)) == True{} : Bool}
  {M3.sc.acc(M3.sc.run(post, M3.sc.step(yy, cc))) == False{} : Bool}

def ins_at(yy, gg, post, cc, hn, hw, hc, hg, ha):
  match yy gg:
    case M3.SOut{+lt, +dd} Laws.GpOut{_ww}:
      by_cls.at(M3.SOut{lt, dd}, Unit{}, post, Unit{}, ha, cc, hn, hw, Lex.classify(cc), {==})
    case M3.SOut{lt, dd} Laws.GpIn{}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SOut{lt, dd}, cc))) == False{} : Bool}, hc)
    case M3.SOut{lt, dd} Laws.GpEsc{}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SOut{lt, dd}, cc))) == False{} : Bool}, hc)
    case M3.SWord{ba, dd} Laws.GpOut{ww}:
      ins_w(ww, ba, dd, post, cc, hn, hw, hc, hg, ha)
    case M3.SWord{ba, dd} Laws.GpIn{}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SWord{ba, dd}, cc))) == False{} : Bool}, hc)
    case M3.SWord{ba, dd} Laws.GpEsc{}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SWord{ba, dd}, cc))) == False{} : Bool}, hc)
    case M3.SIn{dd} Laws.GpOut{ww}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SIn{dd}, cc))) == False{} : Bool}, hc)
    case M3.SIn{dd} Laws.GpIn{}:
      M6.no({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SIn{dd}, cc))) == False{} : Bool}, hg)
    case M3.SIn{dd} Laws.GpEsc{}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SIn{dd}, cc))) == False{} : Bool}, hc)
    case M3.SEsc{dd} Laws.GpOut{ww}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SEsc{dd}, cc))) == False{} : Bool}, hc)
    case M3.SEsc{dd} Laws.GpIn{}:
      Empty.absurd({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SEsc{dd}, cc))) == False{} : Bool}, hc)
    case M3.SEsc{dd} Laws.GpEsc{}:
      M6.no({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SEsc{dd}, cc))) == False{} : Bool}, hg)
    case M3.SBad{} _gg:
      M6.no({M3.sc.acc(M3.sc.run(post, M3.sc.step(M3.SBad{}, cc))) == False{} : Bool}, Equal.trans(Bool, False{},
        M3.sc.acc(M3.sc.run(post, M3.SBad{})), True{}, Equal.sym(Bool, M3.sc.acc(M3.sc.run(post, M3.SBad{})), False{},
            Equal.cong(M3.Sc,
          Bool,
        zz => M3.sc.acc(zz), M3.sc.run(post, M3.SBad{}), M3.SBad{}, sc_bad(post))), ha))

# a text that parses passes the scan
law acc_td2:
  for +txt: String
  for +wa: String
  for +gg: D3.Gv
  for +wb: String
  for e: {txt == wa ++ D3.g.text(gg) ++ wb : String}
  for d: {D3.derived(wa, gg, wb) == True{} : Bool}
  {M3.sc.acc(M3.sc.run(txt, M3.SOut{M3.LSt{}, 0n})) == True{} : Bool}

def acc_td2(txt, wa, gg, wb, e, d):
  Equal.trans(Bool, M3.sc.acc(M3.sc.run(txt, M3.SOut{M3.LSt{}, 0n})), M3.sc.acc(M3.sc.run(wa ++ D3.g.text(gg) ++ wb,
      M3.SOut{M3.LSt{}, 0n})),
    True{}, Equal.cong(String, Bool, zz => M3.sc.acc(M3.sc.run(zz, M3.SOut{M3.LSt{}, 0n})), txt,
        wa ++ D3.g.text(gg) ++ wb, e),
    acc_der(wa, gg, wb, d))

law acc_td:
  for +txt: String
  for r: (&wa: String -> &gg: D3.Gv -> &wb: String -> ({txt == wa ++ D3.g.text(gg) ++ wb : String} &
    {D3.derived(wa, gg, wb) == True{} : Bool}))
  {M3.sc.acc(M3.sc.run(txt, M3.SOut{M3.LSt{}, 0n})) == True{} : Bool}

def acc_td(txt, r):
  (wa, (gg, (wb, (e, d)))) = r
  acc_td2(txt, wa, gg, wb, e, d)

law acc_txt:
  for +txt: String
  for h_s: {D1.short(txt) == True{} : Bool}
  for h_p: {D1.is_some(Ezjson.parse(txt)) == True{} : Bool}
  {M3.sc.acc(M3.sc.run(txt, M3.SOut{M3.LSt{}, 0n})) == True{} : Bool}

def acc_txt(txt, h_s, h_p):
  acc_td(txt, L1.text_derives(txt, h_s, h_p))

# a parse result that is not Some is None
law none_of:
  for +mb: Maybe<&2, V.Json>
  for h: {D1.is_some(mb) == False{} : Bool}
  {mb == None{} : Maybe<&2, V.Json>}

def none_of(mb, h):
  match mb:
    case None{}:
      {==}
    case Some{_jj}:
      Empty.absurd({Some{_jj} == None{} : Maybe<&2, V.Json>}, M1.true_false(h))

# a text the scan does not accept does not parse
law none_by.at:
  for bv: Bool
  for +txt: String
  for e: {D1.is_some(Ezjson.parse(txt)) == bv : Bool}
  for h_t: {D1.short(txt) == True{} : Bool}
  for k: {M3.sc.acc(M3.sc.run(txt, M3.SOut{M3.LSt{}, 0n})) == False{} : Bool}
  {Ezjson.parse(txt) == None{} : Maybe<&2, V.Json>}

def none_by.at(bv, txt, e, h_t, k):
  match bv:
    case True{}:
      Empty.absurd({Ezjson.parse(txt) == None{} : Maybe<&2, V.Json>}, M1.true_false(Equal.trans(Bool, True{},
        M3.sc.acc(M3.sc.run(txt, M3.SOut{M3.LSt{}, 0n})), False{}, Equal.sym(Bool, M3.sc.acc(M3.sc.run(txt,
            M3.SOut{M3.LSt{}, 0n})), True{},
        acc_txt(txt, h_t, e)), k)))
    case False{}:
      none_of(Ezjson.parse(txt), e)

def Laws.ins_none(pre, post, ch, h_p, h_g, h_w, h_n, h_s, h_t):
  k2 = Equal.trans(Bool, M3.sc.acc(M3.sc.run(post, M3.sc.run(pre, M3.SOut{M3.LSt{}, 0n}))),
      M3.sc.acc(M3.sc.run(pre ++ post, M3.SOut{M3.LSt{},
    0n})), True{}, Equal.cong(M3.Sc, Bool,
    zz => M3.sc.acc(zz), M3.sc.run(post, M3.sc.run(pre, M3.SOut{M3.LSt{}, 0n})), M3.sc.run(pre ++ post,
        M3.SOut{M3.LSt{}, 0n}), Equal.sym(M3.Sc,
      M3.sc.run(pre ++ post, M3.SOut{M3.LSt{}, 0n}), M3.sc.run(post, M3.sc.run(pre, M3.SOut{M3.LSt{}, 0n})),
    M3.sc_app(pre, post, M3.SOut{M3.LSt{}, 0n}))), acc_txt(pre ++ post, h_s, h_p))
  k3 = ins_at(M3.sc.run(pre, M3.SOut{M3.LSt{}, 0n}), Laws.gp.run(pre, Laws.GpOut{False{}}), post, ch, h_n, h_w,
      cp_run(pre,
    M3.SOut{M3.LSt{}, 0n}, Laws.GpOut{False{}},
    Unit{}), h_g, k2)
  k4 = Equal.trans(Bool, M3.sc.acc(M3.sc.run(pre ++ SCon{ch, post}, M3.SOut{M3.LSt{}, 0n})),
      M3.sc.acc(M3.sc.run(SCon{ch, post},
    M3.sc.run(pre, M3.SOut{M3.LSt{}, 0n}))), False{},
    Equal.cong(M3.Sc, Bool, zz => M3.sc.acc(zz), M3.sc.run(pre ++ SCon{ch, post}, M3.SOut{M3.LSt{}, 0n}),
        M3.sc.run(SCon{ch, post},
      M3.sc.run(pre, M3.SOut{M3.LSt{}, 0n})), M3.sc_app(pre,
    SCon{ch, post}, M3.SOut{M3.LSt{}, 0n})), k3)
  none_by.at(D1.is_some(Ezjson.parse(pre ++ SCon{ch, post})), pre ++ SCon{ch, post}, {==}, h_t, k4)
