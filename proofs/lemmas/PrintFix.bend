# print's fix of strings is the spec's, and parse builds it back
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ../../src/print.bend as Print
import ../../laws/PrintRoundTrips.bend as L1
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ./CanonicalValue.bend as M1
import ./LexemeOrder.bend as M2
import ./OwnedParse.bend as M3
import ./PrintedStringsParse.bend as M4

# the parser reads a well-formed value's tokens as its canonical form
law parse_tj:
  for +val: V.Json
  for h_wf: {V.wf(val) == True{} : Bool}
  {Parse.finish(Parse.run(M2.tj(val, V.WVal{}), Parse.P{False{}, None{}, Nil{}})) == Some{M1.canon(val,
    V.WVal{})} : Maybe<&2, V.Json>}

def parse_tj(val, h_wf):
  Equal.cong(Parse.P, Maybe<&2, V.Json>, zz => Parse.finish(zz), Parse.run(M2.tj(val, V.WVal{}), Parse.P{False{},
      None{},
    Nil{}}), Parse.P{False{}, Some{M1.canon(val, V.WVal{})}, Nil{}},
    M1.pv_top(val, h_wf))

# fix_eq, with the scalar test named
law fix_eq.go:
  for bb: Bool
  for +uu: U32
  {Bool.pick(Char, Bool.not(bb), Chr{uu}, Chr{65533}) == Bool.pick(Char, bb, Char.from_u32(65533), Chr{uu}) : Char}

def fix_eq.go(bb, _uu):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# print's fix and the spec's are the same
law fix_eq:
  for +ch: Char
  {M2.fix(ch) == D1.fix_char(ch) : Char}

def fix_eq(ch):
  match ch:
    case Chr{+uu}:
      fix_eq.go(D1.non_scalar(uu), uu)

# print's fixs and the spec's fix_str are the same
law fixs_eq:
  for +txt: String
  {M2.fixs(String.to_list(txt)) == D1.fix_str(txt) : String}

def fixs_eq(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      Equal.trans(String, SCon{M2.fix(hd), M2.fixs(String.to_list(tl))}, SCon{D1.fix_char(hd),
          M2.fixs(String.to_list(tl))},
        SCon{D1.fix_char(hd), D1.fix_str(tl)},
        Equal.cong(Char, String, zz => SCon{zz, M2.fixs(String.to_list(tl))}, M2.fix(hd), D1.fix_char(hd), fix_eq(hd)),
        Equal.cong(String, String, zz => SCon{D1.fix_char(hd), zz}, M2.fixs(String.to_list(tl)), D1.fix_str(tl),
          fixs_eq(tl)))

# the value parse builds back is the spec's: owned, strings fixed
law canon_fix:
  for +val: V.Json
  for +sh: V.Shape
  for +h: {V.wf.go(val, sh) == True{} : Bool}
  {M1.canon(val, sh) == D1.fixv(D1.own(val)) : V.Json}

def canon_fix(val, sh, h):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M1.canon(V.JNull{}, V.WArr{}) == D1.fixv(D1.own(V.JNull{})) : V.Json}, h)
        case V.WObj{}:
          M2.no({M1.canon(V.JNull{}, V.WObj{}) == D1.fixv(D1.own(V.JNull{})) : V.Json}, h)
    case V.JBool{bb}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M1.canon(V.JBool{bb}, V.WArr{}) == D1.fixv(D1.own(V.JBool{bb})) : V.Json}, h)
        case V.WObj{}:
          M2.no({M1.canon(V.JBool{bb}, V.WObj{}) == D1.fixv(D1.own(V.JBool{bb})) : V.Json}, h)
    case V.JNum{+raw}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M1.canon(V.JNum{raw}, V.WArr{}) == D1.fixv(D1.own(V.JNum{raw})) : V.Json}, h)
        case V.WObj{}:
          M2.no({M1.canon(V.JNum{raw}, V.WObj{}) == D1.fixv(D1.own(V.JNum{raw})) : V.Json}, h)
    case V.JStr{+txt}:
      match sh:
        case V.WVal{}:
          Equal.cong(String, V.Json, zz => V.JStr{zz}, M2.fixs(String.to_list(txt)), D1.fix_str(txt), fixs_eq(txt))
        case V.WArr{}:
          M2.no({M1.canon(V.JStr{txt}, V.WArr{}) == D1.fixv(D1.own(V.JStr{txt})) : V.Json}, h)
        case V.WObj{}:
          M2.no({M1.canon(V.JStr{txt}, V.WObj{}) == D1.fixv(D1.own(V.JStr{txt})) : V.Json}, h)
    case V.JArr{+items}:
      match sh:
        case V.WVal{}:
          Equal.cong(V.Json, V.Json, zz => V.JArr{zz}, M1.canon(items, V.WArr{}), D1.fixv(D1.own(items)),
            canon_fix(items, V.WArr{}, h))
        case V.WArr{}:
          M2.no({M1.canon(V.JArr{items}, V.WArr{}) == D1.fixv(D1.own(V.JArr{items})) : V.Json}, h)
        case V.WObj{}:
          M2.no({M1.canon(V.JArr{items}, V.WObj{}) == D1.fixv(D1.own(V.JArr{items})) : V.Json}, h)
    case V.JObj{+pairs}:
      match sh:
        case V.WVal{}:
          Equal.cong(V.Json, V.Json, zz => V.JObj{zz}, M1.canon(pairs, V.WObj{}), D1.fixv(D1.own(pairs)),
            canon_fix(pairs, V.WObj{}, h))
        case V.WArr{}:
          M2.no({M1.canon(V.JObj{pairs}, V.WArr{}) == D1.fixv(D1.own(V.JObj{pairs})) : V.Json}, h)
        case V.WObj{}:
          M2.no({M1.canon(V.JObj{pairs}, V.WObj{}) == D1.fixv(D1.own(V.JObj{pairs})) : V.Json}, h)
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          M2.no({M1.canon(V.JNil{}, V.WVal{}) == D1.fixv(D1.own(V.JNil{})) : V.Json}, h)
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JCons{+hd, +tl}:
      match sh:
        case V.WVal{}:
          M2.no({M1.canon(V.JCons{hd, tl}, V.WVal{}) == D1.fixv(D1.own(V.JCons{hd, tl})) : V.Json}, h)
        case V.WArr{}:
          e1 = canon_fix(hd, V.WVal{}, M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(tl, V.WArr{}), h))
          e2 = canon_fix(tl, V.WArr{}, M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(tl, V.WArr{}), h))
          %e1 : {V.JCons{M1.canon(hd, V.WVal{}), M1.canon(tl, V.WArr{})} == V.JCons{_, D1.fixv(D1.own(tl))} : V.Json}
          %e2 : {V.JCons{M1.canon(hd, V.WVal{}), M1.canon(tl, V.WArr{})} == V.JCons{M1.canon(hd, V.WVal{}), _} : V.Json}
          {==}
        case V.WObj{}:
          M2.no({M1.canon(V.JCons{hd, tl}, V.WObj{}) == D1.fixv(D1.own(V.JCons{hd, tl})) : V.Json}, h)
    case V.JPair{+kk, +vv, +rr}:
      match sh:
        case V.WVal{}:
          M2.no({M1.canon(V.JPair{kk, vv, rr}, V.WVal{}) == D1.fixv(D1.own(V.JPair{kk, vv, rr})) : V.Json}, h)
        case V.WArr{}:
          M2.no({M1.canon(V.JPair{kk, vv, rr}, V.WArr{}) == D1.fixv(D1.own(V.JPair{kk, vv, rr})) : V.Json}, h)
        case V.WObj{}:
          e0 = fixs_eq(kk)
          e1 = canon_fix(vv, V.WVal{}, M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(rr, V.WObj{}), h))
          e2 = canon_fix(rr, V.WObj{}, M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(rr, V.WObj{}), h))
          %e0 : {V.JPair{M2.fixs(String.to_list(kk)), M1.canon(vv, V.WVal{}), M1.canon(rr, V.WObj{})} ==
            V.JPair{_, D1.fixv(D1.own(vv)), D1.fixv(D1.own(rr))} : V.Json}
          %e1 : {V.JPair{M2.fixs(String.to_list(kk)), M1.canon(vv, V.WVal{}), M1.canon(rr, V.WObj{})} ==
            V.JPair{M2.fixs(String.to_list(kk)), _, D1.fixv(D1.own(rr))} : V.Json}
          %e2 : {V.JPair{M2.fixs(String.to_list(kk)), M1.canon(vv, V.WVal{}), M1.canon(rr, V.WObj{})} ==
            V.JPair{M2.fixs(String.to_list(kk)), M1.canon(vv, V.WVal{}), _} : V.Json}
          {==}
    case V.JSpan{+src, +nn}:
      match sh:
        case V.WVal{}:
          Equal.cong(String, V.Json, zz => V.JStr{zz}, M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))),
            D1.fix_str(V.span.str(src, nn, U32.is_zero(nn))),
            fixs_eq(V.span.str(src, nn, U32.is_zero(nn))))
        case V.WArr{}:
          M2.no({M1.canon(V.JSpan{src, nn}, V.WArr{}) == D1.fixv(D1.own(V.JSpan{src, nn})) : V.Json}, h)
        case V.WObj{}:
          M2.no({M1.canon(V.JSpan{src, nn}, V.WObj{}) == D1.fixv(D1.own(V.JSpan{src, nn})) : V.Json}, h)
    case V.JBind{+src, +nn, +vv, +rr}:
      match sh:
        case V.WVal{}:
          M2.no({M1.canon(V.JBind{src, nn, vv, rr}, V.WVal{}) == D1.fixv(D1.own(V.JBind{src, nn, vv, rr})) : V.Json}, h)
        case V.WArr{}:
          M2.no({M1.canon(V.JBind{src, nn, vv, rr}, V.WArr{}) == D1.fixv(D1.own(V.JBind{src, nn, vv, rr})) : V.Json}, h)
        case V.WObj{}:
          e0 = fixs_eq(V.span.str(src, nn, U32.is_zero(nn)))
          e1 = canon_fix(vv, V.WVal{}, M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(rr, V.WObj{}), h))
          e2 = canon_fix(rr, V.WObj{}, M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(rr, V.WObj{}), h))
          %e0 : {V.JPair{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), M1.canon(vv, V.WVal{}),
              M1.canon(rr,
            V.WObj{})} ==
            V.JPair{_, D1.fixv(D1.own(vv)), D1.fixv(D1.own(rr))} : V.Json}
          %e1 : {V.JPair{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), M1.canon(vv, V.WVal{}),
              M1.canon(rr,
            V.WObj{})} ==
            V.JPair{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), _, D1.fixv(D1.own(rr))} : V.Json}
          %e2 : {V.JPair{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), M1.canon(vv, V.WVal{}),
              M1.canon(rr,
            V.WObj{})} ==
            V.JPair{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), M1.canon(vv, V.WVal{}), _} : V.Json}
          {==}

# laws/PrintRoundTrips.bend: print then parse gives the value back, owned and fixed
def L1.print_parse(val, h_wf, h_s):
  Equal.trans(Maybe<&2, V.Json>, D1.own_m(Parse.finish(Parse.run(Lex.tokens(Print.print(val)), Parse.P{False{},
    None{}, Nil{}}))), Parse.finish(M3.ownp(Parse.run(Lex.tokens(Print.print(val)), Parse.P{False{}, None{}, Nil{}}))),
    Some{D1.fixv(D1.own(val))}, M3.fin_own(Parse.run(Lex.tokens(Print.print(val)), Parse.P{False{}, None{}, Nil{}})),
    Equal.trans(Maybe<&2, V.Json>, Parse.finish(M3.ownp(Parse.run(Lex.tokens(Print.print(val)), Parse.P{False{}, None{},
      Nil{}}))), Parse.finish(Parse.run(M2.dens(Lex.tokens(Print.print(val))), Parse.P{False{}, None{}, Nil{}})),
      Some{D1.fixv(D1.own(val))}, Equal.cong(Parse.P, Maybe<&2, V.Json>, zz => Parse.finish(zz),
      M3.ownp(Parse.run(Lex.tokens(Print.print(val)), Parse.P{False{}, None{}, Nil{}})),
      Parse.run(M2.dens(Lex.tokens(Print.print(val))), Parse.P{False{}, None{}, Nil{}}),
    M3.run_own(Lex.tokens(Print.print(val)), Parse.P{False{}, None{}, Nil{}})),
    Equal.trans(Maybe<&2, V.Json>, Parse.finish(Parse.run(M2.dens(Lex.tokens(Print.print(val))), Parse.P{False{},
        None{},
      Nil{}})), Parse.finish(Parse.run(M2.tj(val, V.WVal{}), Parse.P{False{}, None{}, Nil{}})),
      Some{D1.fixv(D1.own(val))}, Equal.cong(List<&2, Lex.Tok>, Maybe<&2, V.Json>, zz => Parse.finish(Parse.run(zz,
      Parse.P{False{}, None{}, Nil{}})), M2.dens(Lex.tokens(Print.print(val))), M2.tj(val, V.WVal{}),
    M4.tokens_print(val, h_wf, h_s)),
    Equal.trans(Maybe<&2, V.Json>, Parse.finish(Parse.run(M2.tj(val, V.WVal{}), Parse.P{False{}, None{}, Nil{}})),
      Some{M1.canon(val, V.WVal{})}, Some{D1.fixv(D1.own(val))}, parse_tj(val, h_wf),
    Equal.cong(V.Json, Maybe<&2, V.Json>, zz => Some{zz}, M1.canon(val, V.WVal{}), D1.fixv(D1.own(val)),
    canon_fix(val, V.WVal{}, h_wf))))))
