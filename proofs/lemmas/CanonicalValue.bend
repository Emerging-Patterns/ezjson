# a value as parse builds it back, and fixing its strings
import Base
import ../../src/value.bend as V
import ../../src/lazy.bend as Lazy
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ./DenseTokens.bend as M1
import ./LexemeOrder.bend as M2
import ./ParserReadsTokens.bend as M3
import ./WellFormedCells.bend as M4

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
      V.JStr{M2.fixs(String.to_list(txt))}
    case V.JSpan{src, +nn} V.WVal{}:
      V.JStr{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))}
    case V.JArr{items} V.WVal{}:
      V.JArr{canon(items, V.WArr{})}
    case V.JObj{pairs} V.WVal{}:
      V.JObj{canon(pairs, V.WObj{})}
    case V.JCons{hd, tl} V.WArr{}:
      V.JCons{canon(hd, V.WVal{}), canon(tl, V.WArr{})}
    case V.JPair{kk, vv, rr} V.WObj{}:
      V.JPair{M2.fixs(String.to_list(kk)), canon(vv, V.WVal{}), canon(rr, V.WObj{})}
    case V.JBind{src, +nn, vv, rr} V.WObj{}:
      V.JPair{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), canon(vv, V.WVal{}), canon(rr, V.WObj{})}
    case _ _:
      V.JNil{}

# a value's canonical form is that of its strings fixed
law canon_fx:
  for +val: V.Json
  for +sh: V.Shape
  {canon(val, sh) == M3.canon_r(M1.fxv(val, sh), sh) : V.Json}

def canon_fx(val, sh):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBool{True{}}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBool{False{}}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JNum{+a1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JStr{+a1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JArr{+a1}:
      match sh:
        case V.WVal{}:
          Equal.cong(V.Json, V.Json, zz => V.JArr{zz}, canon(a1, V.WArr{}), M3.canon_r(M1.fxv(a1, V.WArr{}), V.WArr{}),
            canon_fx(a1, V.WArr{}))
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JObj{+a1}:
      match sh:
        case V.WVal{}:
          Equal.cong(V.Json, V.Json, zz => V.JObj{zz}, canon(a1, V.WObj{}), M3.canon_r(M1.fxv(a1, V.WObj{}), V.WObj{}),
            canon_fx(a1, V.WObj{}))
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
    case V.JCons{+a1, +a2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          Equal.trans(V.Json, V.JCons{canon(a1, V.WVal{}), canon(a2, V.WArr{})}, V.JCons{M3.canon_r(M1.fxv(a1,
              V.WVal{}),
            V.WVal{}), canon(a2, V.WArr{})}, V.JCons{M3.canon_r(M1.fxv(a1, V.WVal{}), V.WVal{}), M3.canon_r(M1.fxv(a2,
                V.WArr{}),
            V.WArr{})}, Equal.cong(V.Json, V.Json, zz => V.JCons{zz, canon(a2, V.WArr{})}, canon(a1, V.WVal{}),
            M3.canon_r(M1.fxv(a1, V.WVal{}), V.WVal{}), canon_fx(a1, V.WVal{})), Equal.cong(V.Json, V.Json,
            zz => V.JCons{M3.canon_r(M1.fxv(a1, V.WVal{}), V.WVal{}), zz}, canon(a2, V.WArr{}), M3.canon_r(M1.fxv(a2,
                V.WArr{}),
            V.WArr{}), canon_fx(a2, V.WArr{})))
        case V.WObj{}:
          {==}
    case V.JPair{+a1, +a2, +a3}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.trans(V.Json, V.JPair{M2.fixs(String.to_list(a1)), canon(a2, V.WVal{}), canon(a3, V.WObj{})},
            V.JPair{M2.fixs(String.to_list(a1)), M3.canon_r(M1.fxv(a2, V.WVal{}), V.WVal{}), canon(a3, V.WObj{})},
            V.JPair{M2.fixs(String.to_list(a1)), M3.canon_r(M1.fxv(a2, V.WVal{}), V.WVal{}), M3.canon_r(M1.fxv(a3,
                V.WObj{}),
            V.WObj{})}, Equal.cong(V.Json, V.Json, zz => V.JPair{M2.fixs(String.to_list(a1)), zz, canon(a3, V.WObj{})},
            canon(a2, V.WVal{}), M3.canon_r(M1.fxv(a2, V.WVal{}), V.WVal{}), canon_fx(a2, V.WVal{})), Equal.cong(V.Json,
            V.Json, zz => V.JPair{M2.fixs(String.to_list(a1)), M3.canon_r(M1.fxv(a2, V.WVal{}), V.WVal{}), zz},
                canon(a3,
            V.WObj{}), M3.canon_r(M1.fxv(a3, V.WObj{}), V.WObj{}), canon_fx(a3, V.WObj{})))
    case V.JSpan{+a1, +a2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBind{+a1, +a2, +a3, +a4}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.trans(V.Json, V.JPair{M2.fixs(String.to_list(V.span.str(a1, a2, U32.is_zero(a2)))), canon(a3, V.WVal{}),
            canon(a4, V.WObj{})}, V.JPair{M2.fixs(String.to_list(V.span.str(a1, a2, U32.is_zero(a2)))),
                M3.canon_r(M1.fxv(a3,
            V.WVal{}), V.WVal{}), canon(a4, V.WObj{})}, V.JPair{M2.fixs(String.to_list(V.span.str(a1, a2,
            U32.is_zero(a2)))), M3.canon_r(M1.fxv(a3, V.WVal{}), V.WVal{}), M3.canon_r(M1.fxv(a4, V.WObj{}), V.WObj{})},
            Equal.cong(V.Json, V.Json, zz => V.JPair{M2.fixs(String.to_list(V.span.str(a1, a2, U32.is_zero(a2)))), zz,
            canon(a4, V.WObj{})}, canon(a3, V.WVal{}), M3.canon_r(M1.fxv(a3, V.WVal{}), V.WVal{}), canon_fx(a3,
                V.WVal{})),
            Equal.cong(V.Json, V.Json, zz => V.JPair{M2.fixs(String.to_list(V.span.str(a1, a2, U32.is_zero(a2)))),
            M3.canon_r(M1.fxv(a3, V.WVal{}), V.WVal{}), zz}, canon(a4, V.WObj{}), M3.canon_r(M1.fxv(a4, V.WObj{}),
                V.WObj{}),
            canon_fx(a4, V.WObj{})))

# fixing a value's strings keeps it well-formed
law wf_fx:
  for +val: V.Json
  for +sh: V.Shape
  {V.wf.go(M1.fxv(val, sh), sh) == V.wf.go(val, sh) : Bool}

def wf_fx(val, sh):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBool{True{}}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBool{False{}}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JNum{+a1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JStr{+a1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JArr{+a1}:
      match sh:
        case V.WVal{}:
          wf_fx(a1, V.WArr{})
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JObj{+a1}:
      match sh:
        case V.WVal{}:
          wf_fx(a1, V.WObj{})
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
    case V.JCons{+a1, +a2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          Equal.trans(Bool, Lazy.stop(Bool, Bool.not(V.wf.go(M1.fxv(a1, V.WVal{}), V.WVal{})), False{},
            _u => V.wf.go(M1.fxv(a2, V.WArr{}), V.WArr{})), Lazy.stop(Bool, Bool.not(V.wf.go(a1, V.WVal{})), False{},
            _u => V.wf.go(M1.fxv(a2, V.WArr{}), V.WArr{})), Lazy.stop(Bool, Bool.not(V.wf.go(a1, V.WVal{})), False{},
            _u => V.wf.go(a2, V.WArr{})), Equal.cong(Bool, Bool, zz => Lazy.stop(Bool, Bool.not(zz), False{},
            _u => V.wf.go(M1.fxv(a2, V.WArr{}), V.WArr{})), V.wf.go(M1.fxv(a1, V.WVal{}), V.WVal{}), V.wf.go(a1,
                V.WVal{}),
            wf_fx(a1, V.WVal{})), Equal.cong(Bool, Bool, zz => Lazy.stop(Bool, Bool.not(V.wf.go(a1, V.WVal{})),
            False{}, _u => zz), V.wf.go(M1.fxv(a2, V.WArr{}), V.WArr{}), V.wf.go(a2, V.WArr{}), wf_fx(a2, V.WArr{})))
        case V.WObj{}:
          {==}
    case V.JPair{+a1, +a2, +a3}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.trans(Bool, Lazy.stop(Bool, Bool.not(V.wf.go(M1.fxv(a2, V.WVal{}), V.WVal{})), False{},
            _u => V.wf.go(M1.fxv(a3, V.WObj{}), V.WObj{})), Lazy.stop(Bool, Bool.not(V.wf.go(a2, V.WVal{})), False{},
            _u => V.wf.go(M1.fxv(a3, V.WObj{}), V.WObj{})), Lazy.stop(Bool, Bool.not(V.wf.go(a2, V.WVal{})), False{},
            _u => V.wf.go(a3, V.WObj{})), Equal.cong(Bool, Bool, zz => Lazy.stop(Bool, Bool.not(zz), False{},
            _u => V.wf.go(M1.fxv(a3, V.WObj{}), V.WObj{})), V.wf.go(M1.fxv(a2, V.WVal{}), V.WVal{}), V.wf.go(a2,
                V.WVal{}),
            wf_fx(a2, V.WVal{})), Equal.cong(Bool, Bool, zz => Lazy.stop(Bool, Bool.not(V.wf.go(a2, V.WVal{})),
            False{}, _u => zz), V.wf.go(M1.fxv(a3, V.WObj{}), V.WObj{}), V.wf.go(a3, V.WObj{}), wf_fx(a3, V.WObj{})))
    case V.JSpan{+a1, +a2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBind{+a1, +a2, +a3, +a4}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.trans(Bool, Lazy.stop(Bool, Bool.not(V.wf.go(M1.fxv(a3, V.WVal{}), V.WVal{})), False{},
            _u => V.wf.go(M1.fxv(a4, V.WObj{}), V.WObj{})), Lazy.stop(Bool, Bool.not(V.wf.go(a3, V.WVal{})), False{},
            _u => V.wf.go(M1.fxv(a4, V.WObj{}), V.WObj{})), Lazy.stop(Bool, Bool.not(V.wf.go(a3, V.WVal{})), False{},
            _u => V.wf.go(a4, V.WObj{})), Equal.cong(Bool, Bool, zz => Lazy.stop(Bool, Bool.not(zz), False{},
            _u => V.wf.go(M1.fxv(a4, V.WObj{}), V.WObj{})), V.wf.go(M1.fxv(a3, V.WVal{}), V.WVal{}), V.wf.go(a3,
                V.WVal{}),
            wf_fx(a3, V.WVal{})), Equal.cong(Bool, Bool, zz => Lazy.stop(Bool, Bool.not(V.wf.go(a3, V.WVal{})),
            False{}, _u => zz), V.wf.go(M1.fxv(a4, V.WObj{}), V.WObj{}), V.wf.go(a4, V.WObj{}), wf_fx(a4, V.WObj{})))

# the parser on a value's tokens, from the start, holds the value as its root
law pv_top:
  for +val: V.Json
  for +h_wf: {V.wf(val) == True{} : Bool}
  {Parse.run(M2.tj(val, V.WVal{}), Parse.P{False{}, None{}, Nil{}}) == Parse.P{False{}, Some{canon(val, V.WVal{})},
    Nil{}} : Parse.P}

def pv_top(val, h_wf):
  Equal.trans(Parse.P, Parse.run(M2.tj(val, V.WVal{}), Parse.P{False{}, None{}, Nil{}}), Parse.run(M4.tj_r(M1.fxv(val,
    V.WVal{}), V.WVal{}), Parse.P{False{}, None{}, Nil{}}), Parse.P{False{}, Some{canon(val, V.WVal{})}, Nil{}},
    Equal.cong(List<&2, Lex.Tok>, Parse.P, zz => Parse.run(zz, Parse.P{False{}, None{}, Nil{}}), M2.tj(val, V.WVal{}),
    M4.tj_r(M1.fxv(val, V.WVal{}), V.WVal{}), M1.tj_fx(val, V.WVal{})), Equal.trans(Parse.P,
        Parse.run(M4.tj_r(M1.fxv(val, V.WVal{}),
    V.WVal{}), Parse.P{False{}, None{}, Nil{}}), Parse.P{False{}, Some{M3.canon_r(M1.fxv(val, V.WVal{}), V.WVal{})},
        Nil{}},
    Parse.P{False{}, Some{canon(val, V.WVal{})}, Nil{}}, M3.pv_r(M1.fxv(val, V.WVal{}), V.WVal{}, Equal.trans(Bool,
    V.wf.go(M1.fxv(val, V.WVal{}), V.WVal{}), V.wf.go(val, V.WVal{}), True{}, wf_fx(val, V.WVal{}), h_wf), False{},
    None{}, Nil{}, V.JNil{})({==}), Equal.cong(V.Json, Parse.P, zz => Parse.P{False{}, Some{zz}, Nil{}},
    M3.canon_r(M1.fxv(val, V.WVal{}), V.WVal{}), canon(val, V.WVal{}), Equal.sym(V.Json, canon(val, V.WVal{}),
    M3.canon_r(M1.fxv(val, V.WVal{}), V.WVal{}), canon_fx(val, V.WVal{})))))
