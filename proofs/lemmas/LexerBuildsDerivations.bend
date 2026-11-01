# the lexer's tokens read back as a derivation, whitespace and spans included
import Base
import ../../src/value.bend as V
import ../../main.bend as Ezjson
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ../../laws/BuiltValuesWellFormed.bend as L1
import ../../laws/NumOkIsNumberRule.bend as L2
import ../../laws/ParsesExactlyJsonTexts.bend as L3
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ../../laws/defs/GrammarDerivations.bend as D2
import ./ArrayLength.bend as M1
import ./CharacterClasses.bend as M2
import ./CursorFollowsDerivation.bend as M3
import ./DenseTokens.bend as M4
import ./ErrorToken.bend as M5
import ./LexemeOrder.bend as M6
import ./LexerErrorSticks.bend as M7
import ./NumberDigits.bend as M8
import ./OwnedParse.bend as M9
import ./ParserReadsTokens.bend as M10
import ./ParserStateCloses.bend as M11
import ./StringPieceLexing.bend as M12
import ./WellFormedCells.bend as M13

# whether cells are an array's
def acells(cells: V.Json) -> Bool:
  match cells:
    case V.JNil{}:
      True{}
    case V.JCons{_, rest}:
      acells(rest)
    case _:
      False{}

# whether cells are an object's
def ocells(cells: V.Json) -> Bool:
  match cells:
    case V.JNil{}:
      True{}
    case V.JPair{_, _, rest}:
      ocells(rest)
    case V.JBind{_, _, _, rest}:
      ocells(rest)
    case _:
      False{}

# whether there are cells
def nonnil(cells: V.Json) -> Bool:
  match cells:
    case V.JNil{}:
      False{}
    case _:
      True{}

# an open frame's cells are its kind's, and there are some after a value
def fok(fr: Parse.Frame) -> Bool:
  match fr:
    case Parse.FArr{+items, Parse.SComma{}}:
      Bool.and(nonnil(items), acells(items))
    case Parse.FArr{items, _}:
      acells(items)
    case Parse.FObj{+pairs, _, Parse.SComma{}}:
      Bool.and(nonnil(pairs), ocells(pairs))
    case Parse.FObj{pairs, _, _}:
      ocells(pairs)

# every open frame is as fok says
def sok(stk: List<&2, Parse.Frame>) -> Bool:
  match stk:
    case Nil{}:
      True{}
    case fr <> rest:
      Bool.and(fok(fr), sok(rest))

# the parser's state, unless it failed, has read the tokens racc, reversed,
# and its frames are as sok says
def ti(st: Parse.P, racc: List<&2, Lex.Tok>) -> Type:
  match st:
    case Parse.P{True{}, _, _}:
      Unit
    case Parse.P{False{}, root, stk}:
      ({M9.rs(root, stk) == racc : List<&2, Lex.Tok>} & {sok(stk) == True{} : Bool})

# a failed state holds the invariant
law ti_bad:
  for st: Parse.P
  for +racc: List<&2, Lex.Tok>
  for h: {M7.pbad(st) == True{} : Bool}
  ti(st, racc)

def ti_bad(st, racc, h):
  match st:
    case Parse.P{bb, +root, +stk}:
      match bb:
        case True{}:
          Unit{}
        case False{}:
          M6.no(ti(Parse.P{False{}, root, stk}, racc), h)

# an array cell in front of more cells
law tjc:
  for +xx: V.Json
  for +acc: V.Json
  for hn: {nonnil(acc) == True{} : Bool}
  for ha: {acells(acc) == True{} : Bool}
  {M13.tj_r(V.JCons{xx, acc}, V.WArr{}) == List.append(&2, Lex.Tok, M13.tj_r(xx, V.WVal{}),
      Lex.TComma{} <> M13.tj_r(acc,
    V.WArr{})) : List<&2, Lex.Tok>}

def tjc(xx, acc, hn, ha):
  match acc:
    case V.JNull{}:
      M6.no({M13.tj_r(V.JCons{xx, V.JNull{}}, V.WArr{}) == List.append(&2, Lex.Tok, M13.tj_r(xx, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JNull{}, V.WArr{})) : List<&2, Lex.Tok>}, ha)
    case V.JBool{+y1}:
      M6.no({M13.tj_r(V.JCons{xx, V.JBool{y1}}, V.WArr{}) == List.append(&2, Lex.Tok, M13.tj_r(xx, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JBool{y1}, V.WArr{})) : List<&2, Lex.Tok>}, ha)
    case V.JNum{+y1}:
      M6.no({M13.tj_r(V.JCons{xx, V.JNum{y1}}, V.WArr{}) == List.append(&2, Lex.Tok, M13.tj_r(xx, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JNum{y1}, V.WArr{})) : List<&2, Lex.Tok>}, ha)
    case V.JStr{+y1}:
      M6.no({M13.tj_r(V.JCons{xx, V.JStr{y1}}, V.WArr{}) == List.append(&2, Lex.Tok, M13.tj_r(xx, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JStr{y1}, V.WArr{})) : List<&2, Lex.Tok>}, ha)
    case V.JArr{+y1}:
      M6.no({M13.tj_r(V.JCons{xx, V.JArr{y1}}, V.WArr{}) == List.append(&2, Lex.Tok, M13.tj_r(xx, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JArr{y1}, V.WArr{})) : List<&2, Lex.Tok>}, ha)
    case V.JObj{+y1}:
      M6.no({M13.tj_r(V.JCons{xx, V.JObj{y1}}, V.WArr{}) == List.append(&2, Lex.Tok, M13.tj_r(xx, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JObj{y1}, V.WArr{})) : List<&2, Lex.Tok>}, ha)
    case V.JNil{}:
      M6.no({M13.tj_r(V.JCons{xx, V.JNil{}}, V.WArr{}) == List.append(&2, Lex.Tok, M13.tj_r(xx, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JNil{}, V.WArr{})) : List<&2, Lex.Tok>}, hn)
    case V.JCons{+y1, +y2}:
      {==}
    case V.JPair{+y1, +y2, +y3}:
      M6.no({M13.tj_r(V.JCons{xx, V.JPair{y1, y2, y3}}, V.WArr{}) == List.append(&2, Lex.Tok, M13.tj_r(xx, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JPair{y1, y2, y3}, V.WArr{})) : List<&2, Lex.Tok>}, ha)
    case V.JSpan{+y1, +y2}:
      M6.no({M13.tj_r(V.JCons{xx, V.JSpan{y1, y2}}, V.WArr{}) == List.append(&2, Lex.Tok, M13.tj_r(xx, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JSpan{y1, y2}, V.WArr{})) : List<&2, Lex.Tok>}, ha)
    case V.JBind{+y1, +y2, +y3, +y4}:
      M6.no({M13.tj_r(V.JCons{xx, V.JBind{y1, y2, y3, y4}}, V.WArr{}) == List.append(&2, Lex.Tok, M13.tj_r(xx,
          V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JBind{y1, y2, y3, y4}, V.WArr{})) : List<&2, Lex.Tok>}, ha)

# an object pair in front of more cells
law tjp:
  for +kk: String
  for +vv: V.Json
  for +acc: V.Json
  for hn: {nonnil(acc) == True{} : Bool}
  for ha: {ocells(acc) == True{} : Bool}
  {M13.tj_r(V.JPair{kk, vv, acc}, V.WObj{}) == Lex.TStr{kk} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv,
      V.WVal{}),
    Lex.TComma{} <> M13.tj_r(acc, V.WObj{})) : List<&2, Lex.Tok>}

def tjp(kk, vv, acc, hn, ha):
  match acc:
    case V.JNull{}:
      M6.no({M13.tj_r(V.JPair{kk, vv, V.JNull{}}, V.WObj{}) == Lex.TStr{kk} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JNull{}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JBool{+y1}:
      M6.no({M13.tj_r(V.JPair{kk, vv, V.JBool{y1}}, V.WObj{}) == Lex.TStr{kk} <> Lex.TColon{} <> List.append(&2,
          Lex.Tok,
        M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JBool{y1}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JNum{+y1}:
      M6.no({M13.tj_r(V.JPair{kk, vv, V.JNum{y1}}, V.WObj{}) == Lex.TStr{kk} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JNum{y1}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JStr{+y1}:
      M6.no({M13.tj_r(V.JPair{kk, vv, V.JStr{y1}}, V.WObj{}) == Lex.TStr{kk} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JStr{y1}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JArr{+y1}:
      M6.no({M13.tj_r(V.JPair{kk, vv, V.JArr{y1}}, V.WObj{}) == Lex.TStr{kk} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JArr{y1}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JObj{+y1}:
      M6.no({M13.tj_r(V.JPair{kk, vv, V.JObj{y1}}, V.WObj{}) == Lex.TStr{kk} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JObj{y1}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JNil{}:
      M6.no({M13.tj_r(V.JPair{kk, vv, V.JNil{}}, V.WObj{}) == Lex.TStr{kk} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JNil{}, V.WObj{})) : List<&2, Lex.Tok>}, hn)
    case V.JCons{+y1, +y2}:
      M6.no({M13.tj_r(V.JPair{kk, vv, V.JCons{y1, y2}}, V.WObj{}) == Lex.TStr{kk} <> Lex.TColon{} <> List.append(&2,
          Lex.Tok,
        M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JCons{y1, y2}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JPair{+y1, +y2, +y3}:
      {==}
    case V.JSpan{+y1, +y2}:
      M6.no({M13.tj_r(V.JPair{kk, vv, V.JSpan{y1, y2}}, V.WObj{}) == Lex.TStr{kk} <> Lex.TColon{} <> List.append(&2,
          Lex.Tok,
        M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JSpan{y1, y2}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JBind{+y1, +y2, +y3, +y4}:
      {==}

# an object binding in front of more cells
law tjb:
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for +acc: V.Json
  for hn: {nonnil(acc) == True{} : Bool}
  for ha: {ocells(acc) == True{} : Bool}
  {M13.tj_r(V.JBind{src, nn, vv, acc}, V.WObj{}) == Lex.TStr{V.span.str(src, nn,
    U32.is_zero(nn))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(acc,
    V.WObj{})) : List<&2, Lex.Tok>}

def tjb(src, nn, vv, acc, hn, ha):
  match acc:
    case V.JNull{}:
      M6.no({M13.tj_r(V.JBind{src, nn, vv, V.JNull{}}, V.WObj{}) == Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JNull{}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JBool{+y1}:
      M6.no({M13.tj_r(V.JBind{src, nn, vv, V.JBool{y1}}, V.WObj{}) == Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JBool{y1}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JNum{+y1}:
      M6.no({M13.tj_r(V.JBind{src, nn, vv, V.JNum{y1}}, V.WObj{}) == Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JNum{y1}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JStr{+y1}:
      M6.no({M13.tj_r(V.JBind{src, nn, vv, V.JStr{y1}}, V.WObj{}) == Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JStr{y1}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JArr{+y1}:
      M6.no({M13.tj_r(V.JBind{src, nn, vv, V.JArr{y1}}, V.WObj{}) == Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JArr{y1}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JObj{+y1}:
      M6.no({M13.tj_r(V.JBind{src, nn, vv, V.JObj{y1}}, V.WObj{}) == Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JObj{y1}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JNil{}:
      M6.no({M13.tj_r(V.JBind{src, nn, vv, V.JNil{}}, V.WObj{}) == Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JNil{}, V.WObj{})) : List<&2, Lex.Tok>}, hn)
    case V.JCons{+y1, +y2}:
      M6.no({M13.tj_r(V.JBind{src, nn, vv, V.JCons{y1, y2}}, V.WObj{}) == Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JCons{y1, y2}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JPair{+y1, +y2, +y3}:
      {==}
    case V.JSpan{+y1, +y2}:
      M6.no({M13.tj_r(V.JBind{src, nn, vv, V.JSpan{y1, y2}}, V.WObj{}) == Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JSpan{y1, y2}, V.WObj{})) : List<&2, Lex.Tok>}, ha)
    case V.JBind{+y1, +y2, +y3, +y4}:
      {==}

# array cells reversed onto more cells read as the cells reversed, a comma,
# then the more cells
law rev_a:
  for +items: V.Json
  for +acc: V.Json
  for +hi: {acells(items) == True{} : Bool}
  for +ha: {acells(acc) == True{} : Bool}
  for +hn: {nonnil(acc) == True{} : Bool}
  for +aa: List<&2, Lex.Tok>
  {List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(items, acc), V.WArr{}), aa) == List.reverse.go(&2, Lex.Tok,
      M13.tj_r(acc,
    V.WArr{}), M9.sepr(items, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(items, V.JNil{}), V.WArr{}),
        aa))) : List<&2,
    Lex.Tok>}

def rev_a(items, acc, hi, ha, hn, aa):
  match items:
    case V.JNull{}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JNull{}, acc), V.WArr{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WArr{}), M9.sepr(V.JNull{}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JNull{},
            V.JNil{}),
        V.WArr{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JBool{+x1}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JBool{x1}, acc), V.WArr{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WArr{}), M9.sepr(V.JBool{x1}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JBool{x1},
            V.JNil{}),
        V.WArr{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JNum{+x1}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JNum{x1}, acc), V.WArr{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WArr{}), M9.sepr(V.JNum{x1}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JNum{x1},
            V.JNil{}),
        V.WArr{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JStr{+x1}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JStr{x1}, acc), V.WArr{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WArr{}), M9.sepr(V.JStr{x1}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JStr{x1},
            V.JNil{}),
        V.WArr{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JArr{+x1}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JArr{x1}, acc), V.WArr{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WArr{}), M9.sepr(V.JArr{x1}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JArr{x1},
            V.JNil{}),
        V.WArr{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JObj{+x1}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JObj{x1}, acc), V.WArr{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WArr{}), M9.sepr(V.JObj{x1}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JObj{x1},
            V.JNil{}),
        V.WArr{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2, V.JCons{x1, acc}), V.WArr{}),
          aa),
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.JCons{x1, acc}, V.WArr{}), M9.sepr(x2, List.reverse.go(&2, Lex.Tok,
        M13.tj_r(V.reverse(x2, V.JNil{}), V.WArr{}), aa))), List.reverse.go(&2, Lex.Tok, M13.tj_r(acc, V.WArr{}),
        Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2, V.JCons{x1, V.JNil{}}), V.WArr{}), aa)),
        rev_a(x2, V.JCons{x1, acc}, hi, ha, {==}, aa), Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok,
        M13.tj_r(V.JCons{x1, acc}, V.WArr{}), M9.sepr(x2, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2, V.JNil{}),
        V.WArr{}), aa))), List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(x1, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(acc, V.WArr{})), M9.sepr(x2, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2,
            V.JNil{}),
        V.WArr{}), aa))), List.reverse.go(&2, Lex.Tok, M13.tj_r(acc, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2,
        Lex.Tok, M13.tj_r(V.reverse(x2, V.JCons{x1, V.JNil{}}), V.WArr{}), aa)), Equal.cong(List<&2, Lex.Tok>, List<&2,
        Lex.Tok>, zz => List.reverse.go(&2, Lex.Tok, zz, M9.sepr(x2, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2,
        V.JNil{}), V.WArr{}), aa))), M13.tj_r(V.JCons{x1, acc}, V.WArr{}), List.append(&2, Lex.Tok, M13.tj_r(x1,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(acc, V.WArr{})), tjc(x1, acc, hn, ha)), Equal.trans(List<&2, Lex.Tok>,
            List.reverse.go(&2,
        Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(x1, V.WVal{}), Lex.TComma{} <> M13.tj_r(acc, V.WArr{})), M9.sepr(x2,
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2, V.JNil{}), V.WArr{}), aa))), List.reverse.go(&2, Lex.Tok,
        Lex.TComma{} <> M13.tj_r(acc, V.WArr{}), List.reverse.go(&2, Lex.Tok, M13.tj_r(x1, V.WVal{}), M9.sepr(x2,
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2, V.JNil{}), V.WArr{}), aa)))), List.reverse.go(&2, Lex.Tok,
        M13.tj_r(acc, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2, V.JCons{x1,
            V.JNil{}}),
        V.WArr{}), aa)), M13.rev_app(M13.tj_r(x1, V.WVal{}), Lex.TComma{} <> M13.tj_r(acc, V.WArr{}), M9.sepr(x2,
            List.reverse.go(&2,
        Lex.Tok, M13.tj_r(V.reverse(x2, V.JNil{}), V.WArr{}), aa))), Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2,
        Lex.Tok, Lex.TComma{} <> M13.tj_r(acc, V.WArr{}), List.reverse.go(&2, Lex.Tok, M13.tj_r(x1, V.WVal{}),
            M9.sepr(x2,
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2, V.JNil{}), V.WArr{}), aa)))), List.reverse.go(&2, Lex.Tok,
        M13.tj_r(acc, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.JCons{x1, V.JNil{}}, V.WArr{}),
        M9.sepr(x2, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2, V.JNil{}), V.WArr{}), aa)))),
            List.reverse.go(&2,
        Lex.Tok, M13.tj_r(acc, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2,
            V.JCons{x1,
        V.JNil{}}), V.WArr{}), aa)), {==}, Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.reverse.go(&2,
        Lex.Tok, M13.tj_r(acc, V.WArr{}), Lex.TComma{} <> zz), List.reverse.go(&2, Lex.Tok, M13.tj_r(V.JCons{x1,
            V.JNil{}},
        V.WArr{}), M9.sepr(x2, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2, V.JNil{}), V.WArr{}), aa))),
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2, V.JCons{x1, V.JNil{}}), V.WArr{}), aa), Equal.sym(List<&2,
        Lex.Tok>, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x2, V.JCons{x1, V.JNil{}}), V.WArr{}), aa),
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.JCons{x1, V.JNil{}}, V.WArr{}), M9.sepr(x2, List.reverse.go(&2, Lex.Tok,
        M13.tj_r(V.reverse(x2, V.JNil{}), V.WArr{}), aa))), rev_a(x2, V.JCons{x1, V.JNil{}}, hi, {==}, {==}, aa)))))))
    case V.JPair{+x1, +x2, +x3}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JPair{x1, x2, x3}, acc), V.WArr{}),
          aa) == List.reverse.go(&2,
        Lex.Tok, M13.tj_r(acc, V.WArr{}), M9.sepr(V.JPair{x1, x2, x3}, List.reverse.go(&2, Lex.Tok,
            M13.tj_r(V.reverse(V.JPair{x1,
        x2, x3}, V.JNil{}), V.WArr{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JSpan{+x1, +x2}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JSpan{x1, x2}, acc), V.WArr{}),
          aa) == List.reverse.go(&2,
        Lex.Tok, M13.tj_r(acc, V.WArr{}), M9.sepr(V.JSpan{x1, x2}, List.reverse.go(&2, Lex.Tok,
            M13.tj_r(V.reverse(V.JSpan{x1,
        x2}, V.JNil{}), V.WArr{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JBind{+x1, +x2, +x3, +x4}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JBind{x1, x2, x3, x4}, acc), V.WArr{}),
        aa) == List.reverse.go(&2, Lex.Tok, M13.tj_r(acc, V.WArr{}), M9.sepr(V.JBind{x1, x2, x3, x4},
            List.reverse.go(&2,
        Lex.Tok, M13.tj_r(V.reverse(V.JBind{x1, x2, x3, x4}, V.JNil{}), V.WArr{}), aa))) : List<&2, Lex.Tok>}, hi)

# object cells reversed onto more cells read as the cells reversed, a comma,
# then the more cells
law rev_o:
  for +items: V.Json
  for +acc: V.Json
  for +hi: {ocells(items) == True{} : Bool}
  for +ha: {ocells(acc) == True{} : Bool}
  for +hn: {nonnil(acc) == True{} : Bool}
  for +aa: List<&2, Lex.Tok>
  {List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(items, acc), V.WObj{}), aa) == List.reverse.go(&2, Lex.Tok,
      M13.tj_r(acc,
    V.WObj{}), M9.sepr(items, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(items, V.JNil{}), V.WObj{}),
        aa))) : List<&2,
    Lex.Tok>}

def rev_o(items, acc, hi, ha, hn, aa):
  match items:
    case V.JNull{}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JNull{}, acc), V.WObj{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WObj{}), M9.sepr(V.JNull{}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JNull{},
            V.JNil{}),
        V.WObj{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JBool{+x1}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JBool{x1}, acc), V.WObj{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WObj{}), M9.sepr(V.JBool{x1}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JBool{x1},
            V.JNil{}),
        V.WObj{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JNum{+x1}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JNum{x1}, acc), V.WObj{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WObj{}), M9.sepr(V.JNum{x1}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JNum{x1},
            V.JNil{}),
        V.WObj{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JStr{+x1}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JStr{x1}, acc), V.WObj{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WObj{}), M9.sepr(V.JStr{x1}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JStr{x1},
            V.JNil{}),
        V.WObj{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JArr{+x1}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JArr{x1}, acc), V.WObj{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WObj{}), M9.sepr(V.JArr{x1}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JArr{x1},
            V.JNil{}),
        V.WObj{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JObj{+x1}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JObj{x1}, acc), V.WObj{}), aa) == List.reverse.go(&2,
          Lex.Tok,
        M13.tj_r(acc, V.WObj{}), M9.sepr(V.JObj{x1}, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JObj{x1},
            V.JNil{}),
        V.WObj{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JCons{x1, x2}, acc), V.WObj{}),
          aa) == List.reverse.go(&2,
        Lex.Tok, M13.tj_r(acc, V.WObj{}), M9.sepr(V.JCons{x1, x2}, List.reverse.go(&2, Lex.Tok,
            M13.tj_r(V.reverse(V.JCons{x1,
        x2}, V.JNil{}), V.WObj{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JPair{+x1, +x2, +x3}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3, V.JPair{x1, x2, acc}),
          V.WObj{}),
        aa), List.reverse.go(&2, Lex.Tok, M13.tj_r(V.JPair{x1, x2, acc}, V.WObj{}), M9.sepr(x3, List.reverse.go(&2,
            Lex.Tok,
        M13.tj_r(V.reverse(x3, V.JNil{}), V.WObj{}), aa))), List.reverse.go(&2, Lex.Tok, M13.tj_r(acc, V.WObj{}),
        Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3, V.JPair{x1, x2, V.JNil{}}), V.WObj{}), aa)),
        rev_o(x3, V.JPair{x1, x2, acc}, hi, ha, {==}, aa), Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok,
        M13.tj_r(V.JPair{x1, x2, acc}, V.WObj{}), M9.sepr(x3, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3,
            V.JNil{}),
        V.WObj{}), aa))), List.reverse.go(&2, Lex.Tok, Lex.TStr{x1} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M13.tj_r(x2, V.WVal{}), Lex.TComma{} <> M13.tj_r(acc, V.WObj{})), M9.sepr(x3, List.reverse.go(&2, Lex.Tok,
        M13.tj_r(V.reverse(x3, V.JNil{}), V.WObj{}), aa))), List.reverse.go(&2, Lex.Tok, M13.tj_r(acc, V.WObj{}),
        Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3, V.JPair{x1, x2, V.JNil{}}), V.WObj{}), aa)),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.reverse.go(&2, Lex.Tok, zz, M9.sepr(x3,
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3, V.JNil{}), V.WObj{}), aa))), M13.tj_r(V.JPair{x1, x2, acc},
        V.WObj{}), Lex.TStr{x1} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(acc, V.WObj{})), tjp(x1, x2, acc, hn, ha)), Equal.trans(List<&2, Lex.Tok>,
        List.reverse.go(&2, Lex.Tok, Lex.TStr{x1} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(acc, V.WObj{})), M9.sepr(x3, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3,
            V.JNil{}),
        V.WObj{}), aa))), List.reverse.go(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(acc, V.WObj{}), List.reverse.go(&2,
        Lex.Tok, M13.tj_r(x2, V.WVal{}), Lex.TColon{} <> Lex.TStr{x1} <> M9.sepr(x3, List.reverse.go(&2, Lex.Tok,
        M13.tj_r(V.reverse(x3, V.JNil{}), V.WObj{}), aa)))), List.reverse.go(&2, Lex.Tok, M13.tj_r(acc, V.WObj{}),
        Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3, V.JPair{x1, x2, V.JNil{}}), V.WObj{}), aa)),
        M13.rev_app(M13.tj_r(x2, V.WVal{}), Lex.TComma{} <> M13.tj_r(acc, V.WObj{}),
            Lex.TColon{} <> Lex.TStr{x1} <> M9.sepr(x3,
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3, V.JNil{}), V.WObj{}), aa))), Equal.trans(List<&2, Lex.Tok>,
        List.reverse.go(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(acc, V.WObj{}), List.reverse.go(&2, Lex.Tok, M13.tj_r(x2,
        V.WVal{}), Lex.TColon{} <> Lex.TStr{x1} <> M9.sepr(x3, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3,
            V.JNil{}),
        V.WObj{}), aa)))), List.reverse.go(&2, Lex.Tok, M13.tj_r(acc, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2,
        Lex.Tok, M13.tj_r(V.JPair{x1, x2, V.JNil{}}, V.WObj{}), M9.sepr(x3, List.reverse.go(&2, Lex.Tok,
            M13.tj_r(V.reverse(x3,
        V.JNil{}), V.WObj{}), aa)))), List.reverse.go(&2, Lex.Tok, M13.tj_r(acc, V.WObj{}),
        Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3, V.JPair{x1, x2, V.JNil{}}), V.WObj{}), aa)),
        {==}, Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.reverse.go(&2, Lex.Tok, M13.tj_r(acc,
            V.WObj{}),
        Lex.TComma{} <> zz), List.reverse.go(&2, Lex.Tok, M13.tj_r(V.JPair{x1, x2, V.JNil{}}, V.WObj{}), M9.sepr(x3,
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3, V.JNil{}), V.WObj{}), aa))), List.reverse.go(&2, Lex.Tok,
        M13.tj_r(V.reverse(x3, V.JPair{x1, x2, V.JNil{}}), V.WObj{}), aa), Equal.sym(List<&2, Lex.Tok>,
            List.reverse.go(&2,
        Lex.Tok, M13.tj_r(V.reverse(x3, V.JPair{x1, x2, V.JNil{}}), V.WObj{}), aa), List.reverse.go(&2, Lex.Tok,
        M13.tj_r(V.JPair{x1, x2, V.JNil{}}, V.WObj{}), M9.sepr(x3, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x3,
            V.JNil{}),
        V.WObj{}), aa))), rev_o(x3, V.JPair{x1, x2, V.JNil{}}, hi, {==}, {==}, aa)))))))
    case V.JSpan{+x1, +x2}:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(V.JSpan{x1, x2}, acc), V.WObj{}),
          aa) == List.reverse.go(&2,
        Lex.Tok, M13.tj_r(acc, V.WObj{}), M9.sepr(V.JSpan{x1, x2}, List.reverse.go(&2, Lex.Tok,
            M13.tj_r(V.reverse(V.JSpan{x1,
        x2}, V.JNil{}), V.WObj{}), aa))) : List<&2, Lex.Tok>}, hi)
    case V.JBind{+x1, +x2, +x3, +x4}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JBind{x1, x2, x3, acc}),
        V.WObj{}), aa), List.reverse.go(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2, x3, acc}, V.WObj{}), M9.sepr(x4,
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JNil{}), V.WObj{}), aa))), List.reverse.go(&2, Lex.Tok,
        M13.tj_r(acc, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JBind{x1, x2, x3,
        V.JNil{}}), V.WObj{}), aa)), rev_o(x4, V.JBind{x1, x2, x3, acc}, hi, ha, {==}, aa), Equal.trans(List<&2,
        Lex.Tok>, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2, x3, acc}, V.WObj{}), M9.sepr(x4,
            List.reverse.go(&2,
        Lex.Tok, M13.tj_r(V.reverse(x4, V.JNil{}), V.WObj{}), aa))), List.reverse.go(&2, Lex.Tok,
            Lex.TStr{V.span.str(x1,
        x2, U32.is_zero(x2))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x3, V.WVal{}),
            Lex.TComma{} <> M13.tj_r(acc,
        V.WObj{})), M9.sepr(x4, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JNil{}), V.WObj{}), aa))),
        List.reverse.go(&2, Lex.Tok, M13.tj_r(acc, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
        M13.tj_r(V.reverse(x4, V.JBind{x1, x2, x3, V.JNil{}}), V.WObj{}), aa)), Equal.cong(List<&2, Lex.Tok>, List<&2,
        Lex.Tok>, zz => List.reverse.go(&2, Lex.Tok, zz, M9.sepr(x4, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4,
        V.JNil{}), V.WObj{}), aa))), M13.tj_r(V.JBind{x1, x2, x3, acc}, V.WObj{}), Lex.TStr{V.span.str(x1, x2,
        U32.is_zero(x2))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x3, V.WVal{}),
            Lex.TComma{} <> M13.tj_r(acc,
        V.WObj{})), tjb(x1, x2, x3, acc, hn, ha)), Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok,
        Lex.TStr{V.span.str(x1, x2, U32.is_zero(x2))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x3,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(acc, V.WObj{})), M9.sepr(x4, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4,
            V.JNil{}),
        V.WObj{}), aa))), List.reverse.go(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(acc, V.WObj{}), List.reverse.go(&2,
        Lex.Tok, M13.tj_r(x3, V.WVal{}), Lex.TColon{} <> Lex.TStr{V.span.str(x1, x2, U32.is_zero(x2))} <> M9.sepr(x4,
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JNil{}), V.WObj{}), aa)))), List.reverse.go(&2, Lex.Tok,
        M13.tj_r(acc, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JBind{x1, x2, x3,
        V.JNil{}}), V.WObj{}), aa)), M13.rev_app(M13.tj_r(x3, V.WVal{}), Lex.TComma{} <> M13.tj_r(acc, V.WObj{}),
        Lex.TColon{} <> Lex.TStr{V.span.str(x1, x2, U32.is_zero(x2))} <> M9.sepr(x4, List.reverse.go(&2, Lex.Tok,
        M13.tj_r(V.reverse(x4, V.JNil{}), V.WObj{}), aa))), Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok,
        Lex.TComma{} <> M13.tj_r(acc, V.WObj{}), List.reverse.go(&2, Lex.Tok, M13.tj_r(x3, V.WVal{}),
        Lex.TColon{} <> Lex.TStr{V.span.str(x1, x2, U32.is_zero(x2))} <> M9.sepr(x4, List.reverse.go(&2, Lex.Tok,
        M13.tj_r(V.reverse(x4, V.JNil{}), V.WObj{}), aa)))), List.reverse.go(&2, Lex.Tok, M13.tj_r(acc, V.WObj{}),
        Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2, x3, V.JNil{}}, V.WObj{}), M9.sepr(x4,
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JNil{}), V.WObj{}), aa)))), List.reverse.go(&2, Lex.Tok,
        M13.tj_r(acc, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JBind{x1, x2, x3,
        V.JNil{}}), V.WObj{}), aa)), {==}, Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.reverse.go(&2,
        Lex.Tok, M13.tj_r(acc, V.WObj{}), Lex.TComma{} <> zz), List.reverse.go(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2, x3,
        V.JNil{}}, V.WObj{}), M9.sepr(x4, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JNil{}), V.WObj{}),
            aa))),
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JBind{x1, x2, x3, V.JNil{}}), V.WObj{}), aa),
        Equal.sym(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JBind{x1, x2, x3, V.JNil{}}),
        V.WObj{}), aa), List.reverse.go(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2, x3, V.JNil{}}, V.WObj{}), M9.sepr(x4,
        List.reverse.go(&2, Lex.Tok, M13.tj_r(V.reverse(x4, V.JNil{}), V.WObj{}), aa))), rev_o(x4, V.JBind{x1, x2, x3,
        V.JNil{}}, hi, {==}, {==}, aa)))))))

# put lands a value on the state's tokens, unless it fails
law put_ti:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +vv: V.Json
  for +hs: {sok(stk) == True{} : Bool}
  ti(Parse.put(stk, root, vv, False{}), List.reverse.go(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), M9.rs(root, stk)))

def put_ti(stk, root, vv, hs):
  match stk:
    case Nil{}:
      match root:
        case None{}:
          ({==}, {==})
        case Some{_rr}:
          Unit{}
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, Parse.SValue{}}:
          (rev_a(items, V.JCons{vv, V.JNil{}}, M6.and_left(acells(items), sok(rest), hs), {==}, {==},
            Lex.TOpenArr{} <> M9.srev(rest, M9.rrev(root))), hs)
        case Parse.FArr{+items, Parse.SComma{}}:
          Unit{}
        case Parse.FArr{+items, Parse.SKey{}}:
          Unit{}
        case Parse.FArr{+items, Parse.SColon{}}:
          Unit{}
        case Parse.FObj{+items, Parse.KOwn{+txt}, Parse.SValue{}}:
          (rev_o(items, V.JPair{txt, vv, V.JNil{}}, M6.and_left(ocells(items), sok(rest), hs), {==}, {==},
            Lex.TOpenObj{} <> M9.srev(rest, M9.rrev(root))), hs)
        case Parse.FObj{+items, Parse.KCut{+src, +nn}, Parse.SValue{}}:
          (rev_o(items, V.JBind{src, nn, vv, V.JNil{}}, M6.and_left(ocells(items), sok(rest), hs), {==}, {==},
            Lex.TOpenObj{} <> M9.srev(rest, M9.rrev(root))), hs)
        case Parse.FObj{+items, +ky, Parse.SComma{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SKey{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SColon{}}:
          Unit{}

# ca_ti for one frame, by its cells
law ca_ti.avalue:
  for items: V.Json
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(Parse.FArr{items, Parse.SValue{}} <> rest) == True{} : Bool}
  ti(Parse.close_arr(Parse.FArr{items, Parse.SValue{}} <> rest, root, False{}), Lex.TCloseArr{} <> M9.rs(root,
    Parse.FArr{items, Parse.SValue{}} <> rest))

def ca_ti.avalue(items, rest, root, hs):
  match items:
    case V.JNull{}:
      Unit{}
    case V.JBool{+x1}:
      Unit{}
    case V.JNum{+x1}:
      Unit{}
    case V.JStr{+x1}:
      Unit{}
    case V.JArr{+x1}:
      Unit{}
    case V.JObj{+x1}:
      Unit{}
    case V.JNil{}:
      put_ti(rest, root, V.JArr{V.JNil{}}, hs)
    case V.JCons{+x1, +x2}:
      Unit{}
    case V.JPair{+x1, +x2, +x3}:
      Unit{}
    case V.JSpan{+x1, +x2}:
      Unit{}
    case V.JBind{+x1, +x2, +x3, +x4}:
      Unit{}

# ca_ti for one frame, by its cells
law ca_ti.acomma:
  for items: V.Json
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(Parse.FArr{items, Parse.SComma{}} <> rest) == True{} : Bool}
  ti(Parse.close_arr(Parse.FArr{items, Parse.SComma{}} <> rest, root, False{}), Lex.TCloseArr{} <> M9.rs(root,
    Parse.FArr{items, Parse.SComma{}} <> rest))

def ca_ti.acomma(items, rest, root, hs):
  match items:
    case V.JNull{}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JNull{}, V.JNil{}), V.WArr{}), Lex.TCloseArr{},
          Lex.TOpenArr{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JArr{V.reverse(V.JNull{}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JArr{V.reverse(V.JNull{}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JNull{}),
        acells(V.JNull{})), sok(rest), hs))
    case V.JBool{+x1}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JBool{x1}, V.JNil{}), V.WArr{}), Lex.TCloseArr{},
          Lex.TOpenArr{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JArr{V.reverse(V.JBool{x1}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JArr{V.reverse(V.JBool{x1}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JBool{x1}),
        acells(V.JBool{x1})), sok(rest), hs))
    case V.JNum{+x1}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JNum{x1}, V.JNil{}), V.WArr{}), Lex.TCloseArr{},
          Lex.TOpenArr{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JArr{V.reverse(V.JNum{x1}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JArr{V.reverse(V.JNum{x1}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JNum{x1}),
        acells(V.JNum{x1})), sok(rest), hs))
    case V.JStr{+x1}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JStr{x1}, V.JNil{}), V.WArr{}), Lex.TCloseArr{},
          Lex.TOpenArr{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JArr{V.reverse(V.JStr{x1}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JArr{V.reverse(V.JStr{x1}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JStr{x1}),
        acells(V.JStr{x1})), sok(rest), hs))
    case V.JArr{+x1}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JArr{x1}, V.JNil{}), V.WArr{}), Lex.TCloseArr{},
          Lex.TOpenArr{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JArr{V.reverse(V.JArr{x1}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JArr{V.reverse(V.JArr{x1}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JArr{x1}),
        acells(V.JArr{x1})), sok(rest), hs))
    case V.JObj{+x1}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JObj{x1}, V.JNil{}), V.WArr{}), Lex.TCloseArr{},
          Lex.TOpenArr{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JArr{V.reverse(V.JObj{x1}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JArr{V.reverse(V.JObj{x1}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JObj{x1}),
        acells(V.JObj{x1})), sok(rest), hs))
    case V.JNil{}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JNil{}, V.JNil{}), V.WArr{}), Lex.TCloseArr{},
          Lex.TOpenArr{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JArr{V.reverse(V.JNil{}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JArr{V.reverse(V.JNil{}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JNil{}),
          acells(V.JNil{})),
        sok(rest), hs))
    case V.JCons{+x1, +x2}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JCons{x1, x2}, V.JNil{}), V.WArr{}), Lex.TCloseArr{},
          Lex.TOpenArr{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JArr{V.reverse(V.JCons{x1, x2}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JArr{V.reverse(V.JCons{x1, x2}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JCons{x1, x2}),
        acells(V.JCons{x1, x2})), sok(rest), hs))
    case V.JPair{+x1, +x2, +x3}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JPair{x1, x2, x3}, V.JNil{}), V.WArr{}), Lex.TCloseArr{},
        Lex.TOpenArr{} <> M9.srev(rest, M9.rrev(root))) : ti(Parse.put(rest, root, V.JArr{V.reverse(V.JPair{x1, x2, x3},
        V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JArr{V.reverse(V.JPair{x1, x2, x3}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JPair{x1, x2,
        x3}), acells(V.JPair{x1, x2, x3})), sok(rest), hs))
    case V.JSpan{+x1, +x2}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JSpan{x1, x2}, V.JNil{}), V.WArr{}), Lex.TCloseArr{},
          Lex.TOpenArr{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JArr{V.reverse(V.JSpan{x1, x2}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JArr{V.reverse(V.JSpan{x1, x2}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JSpan{x1, x2}),
        acells(V.JSpan{x1, x2})), sok(rest), hs))
    case V.JBind{+x1, +x2, +x3, +x4}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JBind{x1, x2, x3, x4}, V.JNil{}), V.WArr{}), Lex.TCloseArr{},
        Lex.TOpenArr{} <> M9.srev(rest, M9.rrev(root))) : ti(Parse.put(rest, root, V.JArr{V.reverse(V.JBind{x1, x2, x3,
            x4},
        V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JArr{V.reverse(V.JBind{x1, x2, x3, x4}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JBind{x1,
        x2, x3, x4}), acells(V.JBind{x1, x2, x3, x4})), sok(rest), hs))

# ca_ti for one frame, by its cells
law ca_ti.akey:
  for items: V.Json
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(Parse.FArr{items, Parse.SKey{}} <> rest) == True{} : Bool}
  ti(Parse.close_arr(Parse.FArr{items, Parse.SKey{}} <> rest, root, False{}), Lex.TCloseArr{} <> M9.rs(root,
    Parse.FArr{items, Parse.SKey{}} <> rest))

def ca_ti.akey(items, _rest, _root, _hs):
  match items:
    case V.JNull{}:
      Unit{}
    case V.JBool{+x1}:
      Unit{}
    case V.JNum{+x1}:
      Unit{}
    case V.JStr{+x1}:
      Unit{}
    case V.JArr{+x1}:
      Unit{}
    case V.JObj{+x1}:
      Unit{}
    case V.JNil{}:
      Unit{}
    case V.JCons{+x1, +x2}:
      Unit{}
    case V.JPair{+x1, +x2, +x3}:
      Unit{}
    case V.JSpan{+x1, +x2}:
      Unit{}
    case V.JBind{+x1, +x2, +x3, +x4}:
      Unit{}

# ca_ti for one frame, by its cells
law ca_ti.acolon:
  for items: V.Json
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(Parse.FArr{items, Parse.SColon{}} <> rest) == True{} : Bool}
  ti(Parse.close_arr(Parse.FArr{items, Parse.SColon{}} <> rest, root, False{}), Lex.TCloseArr{} <> M9.rs(root,
    Parse.FArr{items, Parse.SColon{}} <> rest))

def ca_ti.acolon(items, _rest, _root, _hs):
  match items:
    case V.JNull{}:
      Unit{}
    case V.JBool{+x1}:
      Unit{}
    case V.JNum{+x1}:
      Unit{}
    case V.JStr{+x1}:
      Unit{}
    case V.JArr{+x1}:
      Unit{}
    case V.JObj{+x1}:
      Unit{}
    case V.JNil{}:
      Unit{}
    case V.JCons{+x1, +x2}:
      Unit{}
    case V.JPair{+x1, +x2, +x3}:
      Unit{}
    case V.JSpan{+x1, +x2}:
      Unit{}
    case V.JBind{+x1, +x2, +x3, +x4}:
      Unit{}

# co_ti for one frame, by its cells
law co_ti.ovalue:
  for items: V.Json
  for +ky: Parse.Key
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(Parse.FObj{items, ky, Parse.SValue{}} <> rest) == True{} : Bool}
  ti(Parse.close_obj(Parse.FObj{items, ky, Parse.SValue{}} <> rest, root, False{}), Lex.TCloseObj{} <> M9.rs(root,
    Parse.FObj{items, ky, Parse.SValue{}} <> rest))

def co_ti.ovalue(items, _ky, _rest, _root, _hs):
  match items:
    case V.JNull{}:
      Unit{}
    case V.JBool{+x1}:
      Unit{}
    case V.JNum{+x1}:
      Unit{}
    case V.JStr{+x1}:
      Unit{}
    case V.JArr{+x1}:
      Unit{}
    case V.JObj{+x1}:
      Unit{}
    case V.JNil{}:
      Unit{}
    case V.JCons{+x1, +x2}:
      Unit{}
    case V.JPair{+x1, +x2, +x3}:
      Unit{}
    case V.JSpan{+x1, +x2}:
      Unit{}
    case V.JBind{+x1, +x2, +x3, +x4}:
      Unit{}

# co_ti for one frame, by its cells
law co_ti.ocomma:
  for items: V.Json
  for +ky: Parse.Key
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(Parse.FObj{items, ky, Parse.SComma{}} <> rest) == True{} : Bool}
  ti(Parse.close_obj(Parse.FObj{items, ky, Parse.SComma{}} <> rest, root, False{}), Lex.TCloseObj{} <> M9.rs(root,
    Parse.FObj{items, ky, Parse.SComma{}} <> rest))

def co_ti.ocomma(items, _ky, rest, root, hs):
  match items:
    case V.JNull{}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JNull{}, V.JNil{}), V.WObj{}), Lex.TCloseObj{},
          Lex.TOpenObj{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JObj{V.reverse(V.JNull{}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JObj{V.reverse(V.JNull{}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JNull{}),
        ocells(V.JNull{})), sok(rest), hs))
    case V.JBool{+x1}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JBool{x1}, V.JNil{}), V.WObj{}), Lex.TCloseObj{},
          Lex.TOpenObj{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JObj{V.reverse(V.JBool{x1}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JObj{V.reverse(V.JBool{x1}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JBool{x1}),
        ocells(V.JBool{x1})), sok(rest), hs))
    case V.JNum{+x1}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JNum{x1}, V.JNil{}), V.WObj{}), Lex.TCloseObj{},
          Lex.TOpenObj{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JObj{V.reverse(V.JNum{x1}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JObj{V.reverse(V.JNum{x1}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JNum{x1}),
        ocells(V.JNum{x1})), sok(rest), hs))
    case V.JStr{+x1}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JStr{x1}, V.JNil{}), V.WObj{}), Lex.TCloseObj{},
          Lex.TOpenObj{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JObj{V.reverse(V.JStr{x1}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JObj{V.reverse(V.JStr{x1}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JStr{x1}),
        ocells(V.JStr{x1})), sok(rest), hs))
    case V.JArr{+x1}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JArr{x1}, V.JNil{}), V.WObj{}), Lex.TCloseObj{},
          Lex.TOpenObj{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JObj{V.reverse(V.JArr{x1}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JObj{V.reverse(V.JArr{x1}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JArr{x1}),
        ocells(V.JArr{x1})), sok(rest), hs))
    case V.JObj{+x1}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JObj{x1}, V.JNil{}), V.WObj{}), Lex.TCloseObj{},
          Lex.TOpenObj{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JObj{V.reverse(V.JObj{x1}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JObj{V.reverse(V.JObj{x1}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JObj{x1}),
        ocells(V.JObj{x1})), sok(rest), hs))
    case V.JNil{}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JNil{}, V.JNil{}), V.WObj{}), Lex.TCloseObj{},
          Lex.TOpenObj{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JObj{V.reverse(V.JNil{}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JObj{V.reverse(V.JNil{}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JNil{}),
          ocells(V.JNil{})),
        sok(rest), hs))
    case V.JCons{+x1, +x2}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JCons{x1, x2}, V.JNil{}), V.WObj{}), Lex.TCloseObj{},
          Lex.TOpenObj{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JObj{V.reverse(V.JCons{x1, x2}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JObj{V.reverse(V.JCons{x1, x2}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JCons{x1, x2}),
        ocells(V.JCons{x1, x2})), sok(rest), hs))
    case V.JPair{+x1, +x2, +x3}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JPair{x1, x2, x3}, V.JNil{}), V.WObj{}), Lex.TCloseObj{},
        Lex.TOpenObj{} <> M9.srev(rest, M9.rrev(root))) : ti(Parse.put(rest, root, V.JObj{V.reverse(V.JPair{x1, x2, x3},
        V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JObj{V.reverse(V.JPair{x1, x2, x3}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JPair{x1, x2,
        x3}), ocells(V.JPair{x1, x2, x3})), sok(rest), hs))
    case V.JSpan{+x1, +x2}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JSpan{x1, x2}, V.JNil{}), V.WObj{}), Lex.TCloseObj{},
          Lex.TOpenObj{} <> M9.srev(rest,
        M9.rrev(root))) : ti(Parse.put(rest, root, V.JObj{V.reverse(V.JSpan{x1, x2}, V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JObj{V.reverse(V.JSpan{x1, x2}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JSpan{x1, x2}),
        ocells(V.JSpan{x1, x2})), sok(rest), hs))
    case V.JBind{+x1, +x2, +x3, +x4}:
      %M12.rev_snoc_t(M13.tj_r(V.reverse(V.JBind{x1, x2, x3, x4}, V.JNil{}), V.WObj{}), Lex.TCloseObj{},
        Lex.TOpenObj{} <> M9.srev(rest, M9.rrev(root))) : ti(Parse.put(rest, root, V.JObj{V.reverse(V.JBind{x1, x2, x3,
            x4},
        V.JNil{})}, False{}), _)
      put_ti(rest, root, V.JObj{V.reverse(V.JBind{x1, x2, x3, x4}, V.JNil{})}, M6.and_right(Bool.and(nonnil(V.JBind{x1,
        x2, x3, x4}), ocells(V.JBind{x1, x2, x3, x4})), sok(rest), hs))

# co_ti for one frame, by its cells
law co_ti.okey:
  for items: V.Json
  for +ky: Parse.Key
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(Parse.FObj{items, ky, Parse.SKey{}} <> rest) == True{} : Bool}
  ti(Parse.close_obj(Parse.FObj{items, ky, Parse.SKey{}} <> rest, root, False{}), Lex.TCloseObj{} <> M9.rs(root,
    Parse.FObj{items, ky, Parse.SKey{}} <> rest))

def co_ti.okey(items, _ky, rest, root, hs):
  match items:
    case V.JNull{}:
      Unit{}
    case V.JBool{+x1}:
      Unit{}
    case V.JNum{+x1}:
      Unit{}
    case V.JStr{+x1}:
      Unit{}
    case V.JArr{+x1}:
      Unit{}
    case V.JObj{+x1}:
      Unit{}
    case V.JNil{}:
      put_ti(rest, root, V.JObj{V.JNil{}}, hs)
    case V.JCons{+x1, +x2}:
      Unit{}
    case V.JPair{+x1, +x2, +x3}:
      Unit{}
    case V.JSpan{+x1, +x2}:
      Unit{}
    case V.JBind{+x1, +x2, +x3, +x4}:
      Unit{}

# co_ti for one frame, by its cells
law co_ti.ocolon:
  for items: V.Json
  for +ky: Parse.Key
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(Parse.FObj{items, ky, Parse.SColon{}} <> rest) == True{} : Bool}
  ti(Parse.close_obj(Parse.FObj{items, ky, Parse.SColon{}} <> rest, root, False{}), Lex.TCloseObj{} <> M9.rs(root,
    Parse.FObj{items, ky, Parse.SColon{}} <> rest))

def co_ti.ocolon(items, _ky, _rest, _root, _hs):
  match items:
    case V.JNull{}:
      Unit{}
    case V.JBool{+x1}:
      Unit{}
    case V.JNum{+x1}:
      Unit{}
    case V.JStr{+x1}:
      Unit{}
    case V.JArr{+x1}:
      Unit{}
    case V.JObj{+x1}:
      Unit{}
    case V.JNil{}:
      Unit{}
    case V.JCons{+x1, +x2}:
      Unit{}
    case V.JPair{+x1, +x2, +x3}:
      Unit{}
    case V.JSpan{+x1, +x2}:
      Unit{}
    case V.JBind{+x1, +x2, +x3, +x4}:
      Unit{}

# comma_ti for one frame, by its cells
law comma_ti.acomma:
  for items: V.Json
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(Parse.FArr{items, Parse.SComma{}} <> rest) == True{} : Bool}
  ti(Parse.step.comma(Parse.FArr{items, Parse.SComma{}} <> rest, root, False{}), Lex.TComma{} <> M9.rs(root,
    Parse.FArr{items, Parse.SComma{}} <> rest))

def comma_ti.acomma(items, rest, root, hs):
  match items:
    case V.JNull{}:
      ({==}, hs)
    case V.JBool{+x1}:
      ({==}, hs)
    case V.JNum{+x1}:
      ({==}, hs)
    case V.JStr{+x1}:
      ({==}, hs)
    case V.JArr{+x1}:
      ({==}, hs)
    case V.JObj{+x1}:
      ({==}, hs)
    case V.JNil{}:
      M6.no(ti(Parse.step.comma(Parse.FArr{V.JNil{}, Parse.SComma{}} <> rest, root, False{}),
          Lex.TComma{} <> M9.rs(root,
        Parse.FArr{V.JNil{}, Parse.SComma{}} <> rest)), hs)
    case V.JCons{+x1, +x2}:
      ({==}, hs)
    case V.JPair{+x1, +x2, +x3}:
      ({==}, hs)
    case V.JSpan{+x1, +x2}:
      ({==}, hs)
    case V.JBind{+x1, +x2, +x3, +x4}:
      ({==}, hs)

# comma_ti for one frame, by its cells
law comma_ti.ocomma:
  for items: V.Json
  for +ky: Parse.Key
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(Parse.FObj{items, ky, Parse.SComma{}} <> rest) == True{} : Bool}
  ti(Parse.step.comma(Parse.FObj{items, ky, Parse.SComma{}} <> rest, root, False{}), Lex.TComma{} <> M9.rs(root,
    Parse.FObj{items, ky, Parse.SComma{}} <> rest))

def comma_ti.ocomma(items, ky, rest, root, hs):
  match items:
    case V.JNull{}:
      ({==}, hs)
    case V.JBool{+x1}:
      ({==}, hs)
    case V.JNum{+x1}:
      ({==}, hs)
    case V.JStr{+x1}:
      ({==}, hs)
    case V.JArr{+x1}:
      ({==}, hs)
    case V.JObj{+x1}:
      ({==}, hs)
    case V.JNil{}:
      M6.no(ti(Parse.step.comma(Parse.FObj{V.JNil{}, ky, Parse.SComma{}} <> rest, root, False{}),
          Lex.TComma{} <> M9.rs(root,
        Parse.FObj{V.JNil{}, ky, Parse.SComma{}} <> rest)), hs)
    case V.JCons{+x1, +x2}:
      ({==}, hs)
    case V.JPair{+x1, +x2, +x3}:
      ({==}, hs)
    case V.JSpan{+x1, +x2}:
      ({==}, hs)
    case V.JBind{+x1, +x2, +x3, +x4}:
      ({==}, hs)

# an opening bracket where a value may go pushes its frame
law oa_ti:
  for ok: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +hs: {sok(stk) == True{} : Bool}
  ti(Parse.step.open_arr.go(False{}, root, stk, ok), Lex.TOpenArr{} <> M9.rs(root, stk))

def oa_ti(ok, _root, _stk, hs):
  match ok:
    case True{}:
      ({==}, hs)
    case False{}:
      Unit{}

# an opening bracket where a value may go pushes its frame
law oo_ti:
  for ok: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +hs: {sok(stk) == True{} : Bool}
  ti(Parse.step.open_obj.go(False{}, root, stk, ok), Lex.TOpenObj{} <> M9.rs(root, stk))

def oo_ti(ok, _root, _stk, hs):
  match ok:
    case True{}:
      ({==}, hs)
    case False{}:
      Unit{}

# a closing bracket that ends an open array puts it
law ca_ti:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(stk) == True{} : Bool}
  ti(Parse.close_arr(stk, root, False{}), Lex.TCloseArr{} <> M9.rs(root, stk))

def ca_ti(stk, root, hs):
  match stk:
    case Nil{}:
      Unit{}
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, Parse.SValue{}}:
          ca_ti.avalue(items, rest, root, hs)
        case Parse.FArr{+items, Parse.SComma{}}:
          ca_ti.acomma(items, rest, root, hs)
        case Parse.FArr{+items, Parse.SKey{}}:
          ca_ti.akey(items, rest, root, hs)
        case Parse.FArr{+items, Parse.SColon{}}:
          ca_ti.acolon(items, rest, root, hs)
        case Parse.FObj{+items, +ky, Parse.SValue{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SComma{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SKey{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SColon{}}:
          Unit{}

# a closing bracket that ends an open object puts it
law co_ti:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(stk) == True{} : Bool}
  ti(Parse.close_obj(stk, root, False{}), Lex.TCloseObj{} <> M9.rs(root, stk))

def co_ti(stk, root, hs):
  match stk:
    case Nil{}:
      Unit{}
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, Parse.SValue{}}:
          Unit{}
        case Parse.FArr{+items, Parse.SComma{}}:
          Unit{}
        case Parse.FArr{+items, Parse.SKey{}}:
          Unit{}
        case Parse.FArr{+items, Parse.SColon{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SValue{}}:
          co_ti.ovalue(items, ky, rest, root, hs)
        case Parse.FObj{+items, +ky, Parse.SComma{}}:
          co_ti.ocomma(items, ky, rest, root, hs)
        case Parse.FObj{+items, +ky, Parse.SKey{}}:
          co_ti.okey(items, ky, rest, root, hs)
        case Parse.FObj{+items, +ky, Parse.SColon{}}:
          co_ti.ocolon(items, ky, rest, root, hs)

# a colon after a member's name
law colon_ti:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(stk) == True{} : Bool}
  ti(Parse.step.colon(stk, root, False{}), Lex.TColon{} <> M9.rs(root, stk))

def colon_ti(stk, _root, hs):
  match stk:
    case Nil{}:
      Unit{}
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, Parse.SValue{}}:
          Unit{}
        case Parse.FArr{+items, Parse.SComma{}}:
          Unit{}
        case Parse.FArr{+items, Parse.SKey{}}:
          Unit{}
        case Parse.FArr{+items, Parse.SColon{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SValue{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SComma{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SKey{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SColon{}}:
          ({==}, hs)

# a comma after a value
law comma_ti:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hs: {sok(stk) == True{} : Bool}
  ti(Parse.step.comma(stk, root, False{}), Lex.TComma{} <> M9.rs(root, stk))

def comma_ti(stk, root, hs):
  match stk:
    case Nil{}:
      Unit{}
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, Parse.SValue{}}:
          Unit{}
        case Parse.FArr{+items, Parse.SComma{}}:
          comma_ti.acomma(items, rest, root, hs)
        case Parse.FArr{+items, Parse.SKey{}}:
          Unit{}
        case Parse.FArr{+items, Parse.SColon{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SValue{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SComma{}}:
          comma_ti.ocomma(items, ky, rest, root, hs)
        case Parse.FObj{+items, +ky, Parse.SKey{}}:
          Unit{}
        case Parse.FObj{+items, +ky, Parse.SColon{}}:
          Unit{}

# a string: a member's name where one goes, else a value
law str_ti:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +txt: String
  for +hs: {sok(stk) == True{} : Bool}
  ti(Parse.put.str(stk, root, Parse.KOwn{txt}, False{}), Lex.TStr{txt} <> M9.rs(root, stk))

def str_ti(stk, root, txt, hs):
  match stk:
    case Nil{}:
      put_ti([], root, V.JStr{txt}, hs)
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, Parse.SValue{}}:
          put_ti(Parse.FArr{items, Parse.SValue{}} <> rest, root, V.JStr{txt}, hs)
        case Parse.FArr{+items, Parse.SComma{}}:
          put_ti(Parse.FArr{items, Parse.SComma{}} <> rest, root, V.JStr{txt}, hs)
        case Parse.FArr{+items, Parse.SKey{}}:
          put_ti(Parse.FArr{items, Parse.SKey{}} <> rest, root, V.JStr{txt}, hs)
        case Parse.FArr{+items, Parse.SColon{}}:
          put_ti(Parse.FArr{items, Parse.SColon{}} <> rest, root, V.JStr{txt}, hs)
        case Parse.FObj{+items, +ky, Parse.SValue{}}:
          put_ti(Parse.FObj{items, ky, Parse.SValue{}} <> rest, root, V.JStr{txt}, hs)
        case Parse.FObj{+items, +ky, Parse.SComma{}}:
          put_ti(Parse.FObj{items, ky, Parse.SComma{}} <> rest, root, V.JStr{txt}, hs)
        case Parse.FObj{+items, +ky, Parse.SKey{}}:
          ({==}, hs)
        case Parse.FObj{+items, +ky, Parse.SColon{}}:
          put_ti(Parse.FObj{items, ky, Parse.SColon{}} <> rest, root, V.JStr{txt}, hs)

# a word, once whether it is a literal name or a number is known
law sw_ti:
  for ok: Bool
  for +raw: String
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +hs: {sok(stk) == True{} : Bool}
  ti(Parse.step.word.go(raw, Parse.P{False{}, root, stk}, ok), Lex.TWord{raw} <> M9.rs(root, stk))

def sw_ti(ok, raw, root, stk, hs):
  match ok:
    case True{}:
      %Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.reverse.go(&2, Lex.Tok, zz, M9.rs(root, stk)),
        M13.tj_r(Parse.word(raw), V.WVal{}), [Lex.TWord{raw}], M3.tjw.at(String.eq(raw, "null"), String.eq(raw, "true"),
        String.eq(raw, "false"), raw, {==}, {==}, {==})) : ti(Parse.put(stk, root, Parse.word(raw), False{}), _)
      put_ti(stk, root, Parse.word(raw), hs)
    case False{}:
      Unit{}

# one token, spans replaced, on a state that has not failed
law step_ti:
  for tok: Lex.Tok
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +hs: {sok(stk) == True{} : Bool}
  ti(Parse.step(M6.den(tok), Parse.P{False{}, root, stk}), M6.den(tok) <> M9.rs(root, stk))

def step_ti(tok, root, stk, hs):
  match tok:
    case Lex.TOpenArr{}:
      oa_ti(Parse.step.ready(stk, root), root, stk, hs)
    case Lex.TCloseArr{}:
      ca_ti(stk, root, hs)
    case Lex.TOpenObj{}:
      oo_ti(Parse.step.ready(stk, root), root, stk, hs)
    case Lex.TCloseObj{}:
      co_ti(stk, root, hs)
    case Lex.TColon{}:
      colon_ti(stk, root, hs)
    case Lex.TComma{}:
      comma_ti(stk, root, hs)
    case Lex.TStr{+txt}:
      str_ti(stk, root, txt, hs)
    case Lex.TWord{+raw}:
      sw_ti(Parse.word.ok(raw), raw, root, stk, hs)
    case Lex.TStrS{+src, +nn}:
      str_ti(stk, root, V.span.str(src, nn, U32.is_zero(nn)), hs)
    case Lex.TWordS{+src, +nn}:
      sw_ti(Parse.word.ok(V.span.str(src, nn, U32.is_zero(nn))), V.span.str(src, nn, U32.is_zero(nn)), root, stk, hs)
    case Lex.TBad{}:
      Unit{}

# one token, spans replaced, keeps the invariant
law step_gen:
  for st: Parse.P
  for +tok: Lex.Tok
  for +racc: List<&2, Lex.Tok>
  for h: ti(st, racc)
  ti(Parse.step(M6.den(tok), st), M6.den(tok) <> racc)

def step_gen(st, tok, racc, h):
  match st:
    case Parse.P{bb, +root, +stk}:
      match bb:
        case True{}:
          ti_bad(Parse.step(M6.den(tok), Parse.P{True{}, root, stk}), M6.den(tok) <> racc, M7.step_bad(M6.den(tok),
            Parse.P{True{}, root, stk}, {==}))
        case False{}:
          (ee, hs) = h
          %ee : ti(Parse.step(M6.den(tok), Parse.P{False{}, root, stk}), M6.den(tok) <> _)
          step_ti(tok, root, stk, hs)

# every token, spans replaced, keeps the invariant
law run_ti:
  for xs: List<&2, Lex.Tok>
  for +st: Parse.P
  for +racc: List<&2, Lex.Tok>
  for h: ti(st, racc)
  ti(Parse.run(M6.dens(xs), st), List.reverse.go(&2, Lex.Tok, M6.dens(xs), racc))

def run_ti(xs, st, racc, h):
  match xs:
    case Nil{}:
      h
    case +tok <> +tl:
      run_ti(tl, Parse.step(M6.den(tok), st), M6.den(tok) <> racc, step_gen(st, tok, racc, h))

# a finished parse has read its value's tokens, by its frames and root
law fin_go:
  for stk: List<&2, Parse.Frame>
  for root: Maybe<&2, V.Json>
  for +racc: List<&2, Lex.Tok>
  for +jj: V.Json
  for h: ti(Parse.P{False{}, root, stk}, racc)
  for hf: {Parse.finish(Parse.P{False{}, root, stk}) == Some{jj} : Maybe<&2, V.Json>}
  {List.reverse.go(&2, Lex.Tok, M13.tj_r(jj, V.WVal{}), []) == racc : List<&2, Lex.Tok>}

def fin_go(stk, root, racc, jj, h, hf):
  match stk:
    case Nil{}:
      match root:
        case None{}:
          M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(jj, V.WVal{}), []) == racc : List<&2, Lex.Tok>},
              Equal.cong(Maybe<&2,
            V.Json>, Bool, zz => D1.is_some(zz), None{}, Some{jj}, hf))
        case Some{+rr}:
          (ee, _hs) = h
          Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, M13.tj_r(jj, V.WVal{}), []), List.reverse.go(&2,
            Lex.Tok, M13.tj_r(rr, V.WVal{}), []), racc, Equal.cong(V.Json, List<&2, Lex.Tok>, zz => List.reverse.go(&2,
            Lex.Tok, M13.tj_r(zz, V.WVal{}), []), jj, rr, Equal.sym(V.Json, rr, jj, Equal.cong(Maybe<&2, V.Json>,
                V.Json,
            zz => M10.unsome(zz), Some{rr}, Some{jj}, hf))), ee)
    case +fr <> +rest:
      M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(jj, V.WVal{}), []) == racc : List<&2, Lex.Tok>}, Equal.cong(Maybe<&2,
        V.Json>, Bool, zz => D1.is_some(zz), Parse.finish(Parse.P{False{}, root, fr <> rest}),
        Some{jj}, hf))

# a finished parse has read its value's tokens
law fin_ti:
  for st: Parse.P
  for +racc: List<&2, Lex.Tok>
  for +jj: V.Json
  for h: ti(st, racc)
  for hf: {Parse.finish(st) == Some{jj} : Maybe<&2, V.Json>}
  {List.reverse.go(&2, Lex.Tok, M13.tj_r(jj, V.WVal{}), []) == racc : List<&2, Lex.Tok>}

def fin_ti(st, racc, jj, h, hf):
  match st:
    case Parse.P{bb, root, stk}:
      match bb:
        case True{}:
          M6.no({List.reverse.go(&2, Lex.Tok, M13.tj_r(jj, V.WVal{}), []) == racc : List<&2, Lex.Tok>},
              Equal.cong(Maybe<&2,
            V.Json>, Bool, zz => D1.is_some(zz), Parse.finish(Parse.P{True{}, root, stk}), Some{jj},
            hf))
        case False{}:
          fin_go(stk, root, racc, jj, h, hf)

# a list reversed twice
law rr_id:
  for +xs: List<&2, Lex.Tok>
  {List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, xs, []), []) == xs : List<&2, Lex.Tok>}

def rr_id(xs):
  Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, xs, []), []),
    List.append(&2, Lex.Tok, xs, []), xs, M4.rev_rev(xs, [], []), M4.lapp_nil(xs))

# the tokens, spans replaced, of a token list the parser accepts are its
# value's
law parse_toks:
  for +xs: List<&2, Lex.Tok>
  for +jj: V.Json
  for h: {Parse.finish(Parse.run(M6.dens(xs), Parse.P{False{}, None{}, Nil{}})) == Some{jj} : Maybe<&2, V.Json>}
  {M13.tj_r(jj, V.WVal{}) == M6.dens(xs) : List<&2, Lex.Tok>}

def parse_toks(xs, jj, h):
  Equal.trans(List<&2, Lex.Tok>, M13.tj_r(jj, V.WVal{}), List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok,
      M13.tj_r(jj,
    V.WVal{}), []), []), M6.dens(xs), Equal.sym(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2,
    Lex.Tok, M13.tj_r(jj, V.WVal{}), []), []), M13.tj_r(jj, V.WVal{}), rr_id(M13.tj_r(jj, V.WVal{}))),
        Equal.trans(List<&2,
    Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M13.tj_r(jj, V.WVal{}), []), []),
    List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M6.dens(xs), []), []), M6.dens(xs), Equal.cong(List<&2,
    Lex.Tok>, List<&2, Lex.Tok>, zz => List.reverse.go(&2, Lex.Tok, zz, []), List.reverse.go(&2, Lex.Tok, M13.tj_r(jj,
    V.WVal{}), []), List.reverse.go(&2, Lex.Tok, M6.dens(xs), []), fin_ti(Parse.run(M6.dens(xs), Parse.P{False{},
        None{},
    Nil{}}), List.reverse.go(&2, Lex.Tok, M6.dens(xs), []), jj, run_ti(xs, Parse.P{False{}, None{}, Nil{}}, [], ({==},
    {==})), h)), rr_id(M6.dens(xs))))

# lexemes listed last first, and the whitespace before each, as the
# characters they spell, reversed
def ritems(its: List<&2, M6.It>) -> List<&2, Char>:
  match its:
    case Nil{}:
      []
    case M6.It{rws, lx} <> rest:
      M6.rlx(lx, List.append(&2, Char, rws, ritems(rest)))

# pieces listed last first, spelled and reversed onto acc
def rsp(ps: List<&2, D2.Piece>, acc: List<&2, Char>) -> List<&2, Char>:
  match ps:
    case Nil{}:
      acc
    case pc <> rest:
      List.reverse.go(&2, Char, String.to_list(D2.piece.text(pc)), rsp(rest, acc))

# a character by its code
law chr_of:
  for ch: Char
  for +kk: U32
  for ee: {Char.to_u32(ch) == kk : U32}
  {ch == Chr{kk} : Char}

def chr_of(ch, kk, ee):
  match ch:
    case Chr{uu}:
      Equal.cong(U32, Char, zz => Chr{zz}, uu, kk, ee)

# a string's characters reversed onto acc go through an append
law srev_app:
  for +aa: String
  for +bb: String
  for +acc: List<&2, Char>
  {List.reverse.go(&2, Char, String.to_list(aa ++ bb), acc) == List.reverse.go(&2, Char, String.to_list(bb),
    List.reverse.go(&2, Char, String.to_list(aa), acc)) : List<&2, Char>}

def srev_app(aa, bb, acc):
  match aa:
    case SNil{}:
      {==}
    case SCon{+ch, +tl}:
      srev_app(tl, bb, ch <> acc)

# a buffer read back as text, reversed onto acc, is the buffer on acc
law text_rc:
  for +buf: List<&2, Char>
  for +txt: String
  for +acc: List<&2, Char>
  {List.reverse.go(&2, Char, String.to_list(Lex.text.go(buf, txt)), acc) == List.reverse.go(&2, Char,
    String.to_list(txt), List.append(&2, Char, buf, acc)) : List<&2, Char>}

def text_rc(buf, txt, acc):
  match buf:
    case Nil{}:
      {==}
    case +ch <> +tl:
      text_rc(tl, SCon{ch, txt}, acc)

# a string's characters read back from pieces listed last first
law text_pc:
  for +ps: List<&2, D2.Piece>
  for +qs: List<&2, D2.Piece>
  {Lex.text.go(M13.pchars(ps), D2.spelled(qs)) == D2.spelled(List.reverse.go(&2, D2.Piece, ps, qs)) : String}

def text_pc(ps, qs):
  match ps:
    case Nil{}:
      {==}
    case +pc <> +tl:
      text_pc(tl, pc <> qs)

# pieces listed last first, put back in order, spelled and reversed
law spell_rev:
  for +ps: List<&2, D2.Piece>
  for +qs: List<&2, D2.Piece>
  for +acc: List<&2, Char>
  {List.reverse.go(&2, Char, String.to_list(D2.spell(List.reverse.go(&2, D2.Piece, ps, qs))),
    acc) == List.reverse.go(&2, Char, String.to_list(D2.spell(qs)), rsp(ps, acc)) : List<&2, Char>}

def spell_rev(ps, qs, acc):
  match ps:
    case Nil{}:
      {==}
    case +pc <> +tl:
      Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list(D2.spell(List.reverse.go(&2, D2.Piece,
        tl, pc <> qs))), acc), List.reverse.go(&2, Char, String.to_list(D2.spell(pc <> qs)), rsp(tl, acc)),
        List.reverse.go(&2, Char, String.to_list(D2.spell(qs)), List.reverse.go(&2, Char,
        String.to_list(D2.piece.text(pc)), rsp(tl, acc))), spell_rev(tl, pc <> qs, acc),
        srev_app(D2.piece.text(pc), D2.spell(qs), rsp(tl, acc)))

# well spelled pieces stay well spelled put back in order
law spell_ok_rev:
  for +ps: List<&2, D2.Piece>
  for +qs: List<&2, D2.Piece>
  for +hp: {D2.spell_ok(ps) == True{} : Bool}
  for hq: {D2.spell_ok(qs) == True{} : Bool}
  {D2.spell_ok(List.reverse.go(&2, D2.Piece, ps, qs)) == True{} : Bool}

def spell_ok_rev(ps, qs, hp, hq):
  match ps:
    case Nil{}:
      hq
    case +pc <> +tl:
      spell_ok_rev(tl, pc <> qs, M6.and_right(D2.piece.ok(pc), D2.spell_ok(tl), hp),
        M6.and2(D2.piece.ok(pc), D2.spell_ok(qs), M6.and_left(D2.piece.ok(pc), D2.spell_ok(tl), hp), hq))

# whether a class is whitespace's
def is_space(cls: Lex.Class) -> Bool:
  match cls:
    case Lex.CSpace{}:
      True{}
    case _:
      False{}

# whether a class is neither a quotation mark's nor a reverse solidus'
def notqb(cls: Lex.Class) -> Bool:
  match cls:
    case Lex.CQuote{}:
      False{}
    case Lex.CBack{}:
      False{}
    case _:
      True{}

# no class but whitespace's past classify's last test
law cls_space_end:
  for +cp: U32
  for h_c: {Lex.COther{} == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_end(cp, h_c):
  M6.no({D1.is_ws(Chr{cp}) == True{} : Bool}, Equal.cong(Lex.Class, Bool, xx => is_space(xx), Lex.COther{},
    Lex.CSpace{}, h_c))

# classify's test for 9, once its answer is named, read back as whitespace
law cls_space_11:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 9) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Lex.COther{}) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_11(cp, bb, eb, h_c):
  match bb:
    case True{}:
      ek = Equal.sym(U32, cp, 9, M13.ueq(cp, 9, eb))
      %ek : {D1.is_ws(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      cls_space_end(cp, h_c)

# classify's test for 13, once its answer is named, read back as whitespace
law cls_space_10:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 13) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_10(cp, bb, eb, h_c):
  match bb:
    case True{}:
      ek = Equal.sym(U32, cp, 13, M13.ueq(cp, 13, eb))
      %ek : {D1.is_ws(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      cls_space_11(cp, U32.is_eq(cp, 9), {==}, h_c)

# classify's test for 10, once its answer is named, read back as whitespace
law cls_space_9:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 10) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_9(cp, bb, eb, h_c):
  match bb:
    case True{}:
      ek = Equal.sym(U32, cp, 10, M13.ueq(cp, 10, eb))
      %ek : {D1.is_ws(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      cls_space_10(cp, U32.is_eq(cp, 13), {==}, h_c)

# classify's test for 32, once its answer is named, read back as whitespace
law cls_space_8:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 32) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})))) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_8(cp, bb, eb, h_c):
  match bb:
    case True{}:
      ek = Equal.sym(U32, cp, 32, M13.ueq(cp, 32, eb))
      %ek : {D1.is_ws(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      cls_space_9(cp, U32.is_eq(cp, 10), {==}, h_c)

# classify's test for 92, once its answer is named, read back as whitespace
law cls_space_7:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 92) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_7(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      M6.no({D1.is_ws(Chr{cp}) == True{} : Bool}, Equal.cong(Lex.Class, Bool, xx => is_space(xx), Lex.CBack{},
        Lex.CSpace{}, h_c))
    case False{}:
      cls_space_8(cp, U32.is_eq(cp, 32), {==}, h_c)

# classify's test for 34, once its answer is named, read back as whitespace
law cls_space_6:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 34) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})))))) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_6(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      M6.no({D1.is_ws(Chr{cp}) == True{} : Bool}, Equal.cong(Lex.Class, Bool, xx => is_space(xx), Lex.CQuote{},
        Lex.CSpace{}, h_c))
    case False{}:
      cls_space_7(cp, U32.is_eq(cp, 92), {==}, h_c)

# classify's test for 44, once its answer is named, read back as whitespace
law cls_space_5:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 44) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))))) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_5(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      M6.no({D1.is_ws(Chr{cp}) == True{} : Bool}, Equal.cong(Lex.Class, Bool, xx => is_space(xx),
        Lex.CPunct{Lex.TComma{}}, Lex.CSpace{}, h_c))
    case False{}:
      cls_space_6(cp, U32.is_eq(cp, 34), {==}, h_c)

# classify's test for 58, once its answer is named, read back as whitespace
law cls_space_4:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 58) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
    Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp,
    92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10),
    Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9),
    Lex.CSpace{}, Lex.COther{})))))))) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_4(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      M6.no({D1.is_ws(Chr{cp}) == True{} : Bool}, Equal.cong(Lex.Class, Bool, xx => is_space(xx),
        Lex.CPunct{Lex.TColon{}}, Lex.CSpace{}, h_c))
    case False{}:
      cls_space_5(cp, U32.is_eq(cp, 44), {==}, h_c)

# classify's test for 125, once its answer is named, read back as whitespace
law cls_space_3:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 125) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58),
    Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{}))))))))) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_3(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      M6.no({D1.is_ws(Chr{cp}) == True{} : Bool}, Equal.cong(Lex.Class, Bool, xx => is_space(xx),
        Lex.CPunct{Lex.TCloseObj{}}, Lex.CSpace{}, h_c))
    case False{}:
      cls_space_4(cp, U32.is_eq(cp, 58), {==}, h_c)

# classify's test for 123, once its answer is named, read back as whitespace
law cls_space_2:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 123) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 125),
    Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{})))))))))) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_2(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      M6.no({D1.is_ws(Chr{cp}) == True{} : Bool}, Equal.cong(Lex.Class, Bool, xx => is_space(xx),
        Lex.CPunct{Lex.TOpenObj{}}, Lex.CSpace{}, h_c))
    case False{}:
      cls_space_3(cp, U32.is_eq(cp, 125), {==}, h_c)

# classify's test for 93, once its answer is named, read back as whitespace
law cls_space_1:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 93) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 123),
    Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}},
    Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
    Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp,
    92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10),
    Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9),
    Lex.CSpace{}, Lex.COther{}))))))))))) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_1(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      M6.no({D1.is_ws(Chr{cp}) == True{} : Bool}, Equal.cong(Lex.Class, Bool, xx => is_space(xx),
        Lex.CPunct{Lex.TCloseArr{}}, Lex.CSpace{}, h_c))
    case False{}:
      cls_space_2(cp, U32.is_eq(cp, 123), {==}, h_c)

# classify's test for 91, once its answer is named, read back as whitespace
law cls_space_0:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 91) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 93),
    Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 123), Lex.CPunct{Lex.TOpenObj{}},
    Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58),
    Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})))))))))))) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(Chr{cp}) == True{} : Bool}

def cls_space_0(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      M6.no({D1.is_ws(Chr{cp}) == True{} : Bool}, Equal.cong(Lex.Class, Bool, xx => is_space(xx),
        Lex.CPunct{Lex.TOpenArr{}}, Lex.CSpace{}, h_c))
    case False{}:
      cls_space_1(cp, U32.is_eq(cp, 93), {==}, h_c)

# whether an answer is SOk
def isur_sok(key: Lex.Sur) -> Bool:
  match key:
    case Lex.SOk{}:
      True{}
    case _:
      False{}

# whether an answer is SHi
def isur_shi(key: Lex.Sur) -> Bool:
  match key:
    case Lex.SHi{}:
      True{}
    case _:
      False{}

# whether an answer is SLo
def isur_slo(key: Lex.Sur) -> Bool:
  match key:
    case Lex.SLo{}:
      True{}
    case _:
      False{}

# SOk is not SHi
law sur_ne_sok_shi:
  for e: {Lex.SOk{} == Lex.SHi{} : Lex.Sur}
  Empty

def sur_ne_sok_shi(e):
  M1.true_false(Equal.cong(Lex.Sur, Bool, zz => isur_sok(zz), Lex.SOk{}, Lex.SHi{}, e))

# SOk is not SLo
law sur_ne_sok_slo:
  for e: {Lex.SOk{} == Lex.SLo{} : Lex.Sur}
  Empty

def sur_ne_sok_slo(e):
  M1.true_false(Equal.cong(Lex.Sur, Bool, zz => isur_sok(zz), Lex.SOk{}, Lex.SLo{}, e))

# SHi is not SOk
law sur_ne_shi_sok:
  for e: {Lex.SHi{} == Lex.SOk{} : Lex.Sur}
  Empty

def sur_ne_shi_sok(e):
  M1.true_false(Equal.cong(Lex.Sur, Bool, zz => isur_shi(zz), Lex.SHi{}, Lex.SOk{}, e))

# SHi is not SLo
law sur_ne_shi_slo:
  for e: {Lex.SHi{} == Lex.SLo{} : Lex.Sur}
  Empty

def sur_ne_shi_slo(e):
  M1.true_false(Equal.cong(Lex.Sur, Bool, zz => isur_shi(zz), Lex.SHi{}, Lex.SLo{}, e))

# SLo is not SOk
law sur_ne_slo_sok:
  for e: {Lex.SLo{} == Lex.SOk{} : Lex.Sur}
  Empty

def sur_ne_slo_sok(e):
  M1.true_false(Equal.cong(Lex.Sur, Bool, zz => isur_slo(zz), Lex.SLo{}, Lex.SOk{}, e))

# SLo is not SHi
law sur_ne_slo_shi:
  for e: {Lex.SLo{} == Lex.SHi{} : Lex.Sur}
  Empty

def sur_ne_slo_shi(e):
  M1.true_false(Equal.cong(Lex.Sur, Bool, zz => isur_slo(zz), Lex.SLo{}, Lex.SHi{}, e))

# a character classify reads as whitespace is whitespace
law cls_space:
  for ch: Char
  for h_c: {Lex.classify(ch) == Lex.CSpace{} : Lex.Class}
  {D1.is_ws(ch) == True{} : Bool}

def cls_space(ch, h_c):
  match ch:
    case Chr{+uu}:
      cls_space_0(uu, U32.is_eq(uu, 91), {==}, h_c)

# a character that is no quotation mark, reverse solidus or control is one a
# string keeps, once its tests are named
law rawc.at:
  for +uu: U32
  for b34: Bool
  for b92: Bool
  for e34: {U32.is_eq(uu, 34) == b34 : Bool}
  for e92: {U32.is_eq(uu, 92) == b92 : Bool}
  for cls: Lex.Class
  for e: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  for hq: {notqb(cls) == True{} : Bool}
  for hlt: {U32.is_lt(uu, 32) == False{} : Bool}
  {D1.raw_char(Chr{uu}) == True{} : Bool}

def rawc.at(uu, b34, b92, e34, e92, cls, e, hq, hlt):
  match b34:
    case True{}:
      cq = Equal.trans(Lex.Class, Lex.classify(Chr{34}), Lex.classify(Chr{uu}), cls, Equal.cong(U32, Lex.Class,
        zz => Lex.classify(Chr{zz}), 34, uu, Equal.sym(U32, uu, 34, M13.ueq(uu, 34, e34))), e)
      M6.no({D1.raw_char(Chr{uu}) == True{} : Bool}, Equal.trans(Bool, False{}, notqb(cls), True{},
          Equal.cong(Lex.Class,
        Bool, zz => notqb(zz), Lex.CQuote{}, cls, cq), hq))
    case False{}:
      match b92:
        case True{}:
          cq = Equal.trans(Lex.Class, Lex.classify(Chr{92}), Lex.classify(Chr{uu}), cls, Equal.cong(U32, Lex.Class,
            zz => Lex.classify(Chr{zz}), 92, uu, Equal.sym(U32, uu, 92, M13.ueq(uu, 92, e92))), e)
          M6.no({D1.raw_char(Chr{uu}) == True{} : Bool}, Equal.trans(Bool, False{}, notqb(cls), True{},
            Equal.cong(Lex.Class, Bool, zz => notqb(zz), Lex.CBack{}, cls, cq), hq))
        case False{}:
          s34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, e34)
          s92 = Equal.sym(Bool, U32.is_eq(uu, 92), False{}, e92)
          slt = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, hlt)
          %s34 : {Bool.not(Bool.or(_, Bool.or(U32.is_eq(uu, 92), U32.is_lt(uu, 32)))) == True{} : Bool}
          %s92 : {Bool.not(Bool.or(False{}, Bool.or(_, U32.is_lt(uu, 32)))) == True{} : Bool}
          %slt : {Bool.not(Bool.or(False{}, Bool.or(False{}, _))) == True{} : Bool}
          {==}

# a character that is no quotation mark, reverse solidus or control is one a
# string keeps
law rawc:
  for ch: Char
  for cls: Lex.Class
  for e: {Lex.classify(ch) == cls : Lex.Class}
  for hq: {notqb(cls) == True{} : Bool}
  for hlt: {U32.is_lt(Char.to_u32(ch), 32) == False{} : Bool}
  {D1.raw_char(ch) == True{} : Bool}

def rawc(ch, cls, e, hq, hlt):
  match ch:
    case Chr{+uu}:
      rawc.at(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), {==}, {==}, cls, e, hq, hlt)

# what unicode.sur's answer says of the comparisons
def surg(b1: Bool, b2: Bool, b3: Bool, b4: Bool, key: Lex.Sur) -> Type:
  match key:
    case Lex.SOk{}:
      {Bool.and(Bool.not(Bool.and(b1, b2)), Bool.not(Bool.and(b3, b4))) == True{} : Bool}
    case Lex.SHi{}:
      {Bool.and(b1, b2) == True{} : Bool}
    case Lex.SLo{}:
      {Bool.and(Bool.not(Bool.and(b1, b2)), Bool.and(b3, b4)) == True{} : Bool}

# a surrogate test's answer, by its comparisons
law sur_at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for key: Lex.Sur
  for e: {M9.sb(b1, b2, b3, b4) == key : Lex.Sur}
  surg(b1, b2, b3, b4, key)

def sur_at(b1, b2, b3, b4, key, e):
  match b1 b2 b3 b4 key:
    case True{} True{} True{} True{} Lex.SOk{}:
      Empty.absurd(surg(True{}, True{}, True{}, True{}, Lex.SOk{}), sur_ne_shi_sok(e))
    case True{} True{} True{} True{} Lex.SHi{}:
      {==}
    case True{} True{} True{} True{} Lex.SLo{}:
      Empty.absurd(surg(True{}, True{}, True{}, True{}, Lex.SLo{}), sur_ne_shi_slo(e))
    case True{} True{} True{} False{} Lex.SOk{}:
      Empty.absurd(surg(True{}, True{}, True{}, False{}, Lex.SOk{}), sur_ne_shi_sok(e))
    case True{} True{} True{} False{} Lex.SHi{}:
      {==}
    case True{} True{} True{} False{} Lex.SLo{}:
      Empty.absurd(surg(True{}, True{}, True{}, False{}, Lex.SLo{}), sur_ne_shi_slo(e))
    case True{} True{} False{} True{} Lex.SOk{}:
      Empty.absurd(surg(True{}, True{}, False{}, True{}, Lex.SOk{}), sur_ne_shi_sok(e))
    case True{} True{} False{} True{} Lex.SHi{}:
      {==}
    case True{} True{} False{} True{} Lex.SLo{}:
      Empty.absurd(surg(True{}, True{}, False{}, True{}, Lex.SLo{}), sur_ne_shi_slo(e))
    case True{} True{} False{} False{} Lex.SOk{}:
      Empty.absurd(surg(True{}, True{}, False{}, False{}, Lex.SOk{}), sur_ne_shi_sok(e))
    case True{} True{} False{} False{} Lex.SHi{}:
      {==}
    case True{} True{} False{} False{} Lex.SLo{}:
      Empty.absurd(surg(True{}, True{}, False{}, False{}, Lex.SLo{}), sur_ne_shi_slo(e))
    case True{} False{} True{} True{} Lex.SOk{}:
      Empty.absurd(surg(True{}, False{}, True{}, True{}, Lex.SOk{}), sur_ne_slo_sok(e))
    case True{} False{} True{} True{} Lex.SHi{}:
      Empty.absurd(surg(True{}, False{}, True{}, True{}, Lex.SHi{}), sur_ne_slo_shi(e))
    case True{} False{} True{} True{} Lex.SLo{}:
      {==}
    case True{} False{} True{} False{} Lex.SOk{}:
      {==}
    case True{} False{} True{} False{} Lex.SHi{}:
      Empty.absurd(surg(True{}, False{}, True{}, False{}, Lex.SHi{}), sur_ne_sok_shi(e))
    case True{} False{} True{} False{} Lex.SLo{}:
      Empty.absurd(surg(True{}, False{}, True{}, False{}, Lex.SLo{}), sur_ne_sok_slo(e))
    case True{} False{} False{} True{} Lex.SOk{}:
      {==}
    case True{} False{} False{} True{} Lex.SHi{}:
      Empty.absurd(surg(True{}, False{}, False{}, True{}, Lex.SHi{}), sur_ne_sok_shi(e))
    case True{} False{} False{} True{} Lex.SLo{}:
      Empty.absurd(surg(True{}, False{}, False{}, True{}, Lex.SLo{}), sur_ne_sok_slo(e))
    case True{} False{} False{} False{} Lex.SOk{}:
      {==}
    case True{} False{} False{} False{} Lex.SHi{}:
      Empty.absurd(surg(True{}, False{}, False{}, False{}, Lex.SHi{}), sur_ne_sok_shi(e))
    case True{} False{} False{} False{} Lex.SLo{}:
      Empty.absurd(surg(True{}, False{}, False{}, False{}, Lex.SLo{}), sur_ne_sok_slo(e))
    case False{} True{} True{} True{} Lex.SOk{}:
      Empty.absurd(surg(False{}, True{}, True{}, True{}, Lex.SOk{}), sur_ne_slo_sok(e))
    case False{} True{} True{} True{} Lex.SHi{}:
      Empty.absurd(surg(False{}, True{}, True{}, True{}, Lex.SHi{}), sur_ne_slo_shi(e))
    case False{} True{} True{} True{} Lex.SLo{}:
      {==}
    case False{} True{} True{} False{} Lex.SOk{}:
      {==}
    case False{} True{} True{} False{} Lex.SHi{}:
      Empty.absurd(surg(False{}, True{}, True{}, False{}, Lex.SHi{}), sur_ne_sok_shi(e))
    case False{} True{} True{} False{} Lex.SLo{}:
      Empty.absurd(surg(False{}, True{}, True{}, False{}, Lex.SLo{}), sur_ne_sok_slo(e))
    case False{} True{} False{} True{} Lex.SOk{}:
      {==}
    case False{} True{} False{} True{} Lex.SHi{}:
      Empty.absurd(surg(False{}, True{}, False{}, True{}, Lex.SHi{}), sur_ne_sok_shi(e))
    case False{} True{} False{} True{} Lex.SLo{}:
      Empty.absurd(surg(False{}, True{}, False{}, True{}, Lex.SLo{}), sur_ne_sok_slo(e))
    case False{} True{} False{} False{} Lex.SOk{}:
      {==}
    case False{} True{} False{} False{} Lex.SHi{}:
      Empty.absurd(surg(False{}, True{}, False{}, False{}, Lex.SHi{}), sur_ne_sok_shi(e))
    case False{} True{} False{} False{} Lex.SLo{}:
      Empty.absurd(surg(False{}, True{}, False{}, False{}, Lex.SLo{}), sur_ne_sok_slo(e))
    case False{} False{} True{} True{} Lex.SOk{}:
      Empty.absurd(surg(False{}, False{}, True{}, True{}, Lex.SOk{}), sur_ne_slo_sok(e))
    case False{} False{} True{} True{} Lex.SHi{}:
      Empty.absurd(surg(False{}, False{}, True{}, True{}, Lex.SHi{}), sur_ne_slo_shi(e))
    case False{} False{} True{} True{} Lex.SLo{}:
      {==}
    case False{} False{} True{} False{} Lex.SOk{}:
      {==}
    case False{} False{} True{} False{} Lex.SHi{}:
      Empty.absurd(surg(False{}, False{}, True{}, False{}, Lex.SHi{}), sur_ne_sok_shi(e))
    case False{} False{} True{} False{} Lex.SLo{}:
      Empty.absurd(surg(False{}, False{}, True{}, False{}, Lex.SLo{}), sur_ne_sok_slo(e))
    case False{} False{} False{} True{} Lex.SOk{}:
      {==}
    case False{} False{} False{} True{} Lex.SHi{}:
      Empty.absurd(surg(False{}, False{}, False{}, True{}, Lex.SHi{}), sur_ne_sok_shi(e))
    case False{} False{} False{} True{} Lex.SLo{}:
      Empty.absurd(surg(False{}, False{}, False{}, True{}, Lex.SLo{}), sur_ne_sok_slo(e))
    case False{} False{} False{} False{} Lex.SOk{}:
      {==}
    case False{} False{} False{} False{} Lex.SHi{}:
      Empty.absurd(surg(False{}, False{}, False{}, False{}, Lex.SHi{}), sur_ne_sok_shi(e))
    case False{} False{} False{} False{} Lex.SLo{}:
      Empty.absurd(surg(False{}, False{}, False{}, False{}, Lex.SLo{}), sur_ne_sok_slo(e))

# unicode.sur is sb of its comparisons
law sur_sb:
  for +cp: U32
  for b1: Bool
  for b2: Bool
  {Lex.unicode.sur.hi(cp, b1, b2) == M9.sb(b1, b2, U32.is_ge(cp, 56320), U32.is_le(cp, 57343)) : Lex.Sur}

def sur_sb(_cp, b1, b2):
  match b1 b2:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# what unicode.sur's answer says of a code point
def surc(+cp: U32, key: Lex.Sur) -> Type:
  match key:
    case Lex.SOk{}:
      {D2.non_sur(cp) == True{} : Bool}
    case Lex.SHi{}:
      {D2.in_hi(cp) == True{} : Bool}
    case Lex.SLo{}:
      {D2.lo_sur(cp) == True{} : Bool}

# unicode.sur's answer read back
law sur_inv:
  for +cp: U32
  for key: Lex.Sur
  for e: {Lex.unicode.sur(cp) == key : Lex.Sur}
  surc(cp, key)

def sur_inv(cp, key, e):
  match key:
    case Lex.SOk{}:
      sur_at(U32.is_ge(cp, 55296), U32.is_le(cp, 56319), U32.is_ge(cp, 56320), U32.is_le(cp, 57343), Lex.SOk{},
        Equal.trans(Lex.Sur, M9.sb(U32.is_ge(cp, 55296), U32.is_le(cp, 56319), U32.is_ge(cp, 56320), U32.is_le(cp,
        57343)), Lex.unicode.sur(cp), Lex.SOk{}, Equal.sym(Lex.Sur, Lex.unicode.sur(cp), M9.sb(U32.is_ge(cp, 55296),
        U32.is_le(cp, 56319), U32.is_ge(cp, 56320), U32.is_le(cp, 57343)), sur_sb(cp, U32.is_ge(cp, 55296),
        U32.is_le(cp, 56319))), e))
    case Lex.SHi{}:
      sur_at(U32.is_ge(cp, 55296), U32.is_le(cp, 56319), U32.is_ge(cp, 56320), U32.is_le(cp, 57343), Lex.SHi{},
        Equal.trans(Lex.Sur, M9.sb(U32.is_ge(cp, 55296), U32.is_le(cp, 56319), U32.is_ge(cp, 56320), U32.is_le(cp,
        57343)), Lex.unicode.sur(cp), Lex.SHi{}, Equal.sym(Lex.Sur, Lex.unicode.sur(cp), M9.sb(U32.is_ge(cp, 55296),
        U32.is_le(cp, 56319), U32.is_ge(cp, 56320), U32.is_le(cp, 57343)), sur_sb(cp, U32.is_ge(cp, 55296),
        U32.is_le(cp, 56319))), e))
    case Lex.SLo{}:
      sur_at(U32.is_ge(cp, 55296), U32.is_le(cp, 56319), U32.is_ge(cp, 56320), U32.is_le(cp, 57343), Lex.SLo{},
        Equal.trans(Lex.Sur, M9.sb(U32.is_ge(cp, 55296), U32.is_le(cp, 56319), U32.is_ge(cp, 56320), U32.is_le(cp,
        57343)), Lex.unicode.sur(cp), Lex.SLo{}, Equal.sym(Lex.Sur, Lex.unicode.sur(cp), M9.sb(U32.is_ge(cp, 55296),
        U32.is_le(cp, 56319), U32.is_ge(cp, 56320), U32.is_le(cp, 57343)), sur_sb(cp, U32.is_ge(cp, 55296),
        U32.is_le(cp, 56319))), e))

# the digits of a \u escape read so far, by how many are left, and what the
# text read so far is: them on top of pre
def uj(left: Nat, +acc: U32, +pre: List<&2, Char>, +rc: List<&2, Char>) -> Type:
  match left:
    case 0n:
      &d1: Char -> &d2: Char -> &d3: Char -> ({D2.hexd(d1) == True{} : Bool} & ({D2.hexd(d2) == True{} : Bool} &
        ({D2.hexd(d3) == True{} : Bool} & ({acc == D2.hex.acc(D2.hex.acc(D2.hex.acc(0, d1), d2), d3) : U32} &
        {rc == d3 <> d2 <> d1 <> pre : List<&2, Char>}))))
    case 1n+l1:
      match l1:
        case 0n:
          &d1: Char -> &d2: Char -> ({D2.hexd(d1) == True{} : Bool} & ({D2.hexd(d2) == True{} : Bool} &
            ({acc == D2.hex.acc(D2.hex.acc(0, d1), d2) : U32} & {rc == d2 <> d1 <> pre : List<&2, Char>})))
        case 1n+l2:
          match l2:
            case 0n:
              &d1: Char -> ({D2.hexd(d1) == True{} : Bool} & ({acc == D2.hex.acc(0, d1) : U32} &
                {rc == d1 <> pre : List<&2, Char>}))
            case 1n+l3:
              match l3:
                case 0n:
                  ({acc == 0 : U32} & {rc == pre : List<&2, Char>})
                case 1n+_l4:
                  Empty

# a high surrogate's four digits
def hj(+hi: U32, +h1: Char, +h2: Char, +h3: Char, +h4: Char) -> Type:
  ({D2.hexd(h1) == True{} : Bool} & ({D2.hexd(h2) == True{} : Bool} & ({D2.hexd(h3) == True{} : Bool} &
    ({D2.hexd(h4) == True{} : Bool} & ({hi == D2.hex4(h1, h2, h3, h4) : U32} & {D2.in_hi(hi) == True{} :
    Bool})))))

# the lexer's state, by its mode, as lexemes read and what is read since, the
# text read so far reversed as rc
def jm(md: Lex.Mode, +buf: List<&2, Char>, +toks: List<&2, Lex.Tok>, +rc: List<&2, Char>) -> Type:
  match md:
    case Lex.Idle{}:
      &its: List<&2, M6.It> -> &rws: List<&2, Char> -> (M13.ic(its, rws, toks) & {rc == List.append(&2, Char, rws,
        ritems(its)) : List<&2, Char>})
    case Lex.Word{}:
      &its: List<&2, M6.It> -> &rws: List<&2, Char> -> (M13.ic(its, rws, toks) & {rc == List.append(&2, Char, buf,
        List.append(&2, Char, rws, ritems(its))) : List<&2, Char>})
    case Lex.Str{}:
      &its: List<&2, M6.It> -> &rws: List<&2, Char> -> &ps: List<&2, D2.Piece> -> (M13.sc(its, rws, ps, buf,
        toks) & {rc == rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))) : List<&2, Char>})
    case Lex.Esc{}:
      &its: List<&2, M6.It> -> &rws: List<&2, Char> -> &ps: List<&2, D2.Piece> -> (M13.sc(its, rws, ps, buf,
        toks) & {rc == '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))) : List<&2, Char>})
    case Lex.Uni{left, acc}:
      &its: List<&2, M6.It> -> &rws: List<&2, Char> -> &ps: List<&2, D2.Piece> -> (M13.sc(its, rws, ps, buf,
        toks) & uj(left, acc, 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))), rc))
    case Lex.Hi{hi}:
      &its: List<&2, M6.It> -> &rws: List<&2, Char> -> &ps: List<&2,
        D2.Piece> -> &h1: Char -> &h2: Char -> &h3: Char -> &h4: Char -> (M13.sc(its, rws, ps, buf,
        toks) & (hj(hi, h1, h2, h3, h4) & {rc == h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2,
          Char, rws, ritems(its))) : List<&2, Char>}))
    case Lex.HiEsc{hi}:
      &its: List<&2, M6.It> -> &rws: List<&2, Char> -> &ps: List<&2,
        D2.Piece> -> &h1: Char -> &h2: Char -> &h3: Char -> &h4: Char -> (M13.sc(its, rws, ps, buf,
        toks) & (hj(hi, h1, h2, h3, h4) & {rc == '\\' <> h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps,
          '"' <> List.append(&2, Char, rws, ritems(its))) : List<&2, Char>}))
    case Lex.Lo{left, acc, hi}:
      &its: List<&2, M6.It> -> &rws: List<&2, Char> -> &ps: List<&2,
        D2.Piece> -> &h1: Char -> &h2: Char -> &h3: Char -> &h4: Char -> (M13.sc(its, rws, ps, buf,
        toks) & (hj(hi, h1, h2, h3, h4) & uj(left, acc, 'u' <> '\\' <> h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps,
          '"' <> List.append(&2, Char, rws, ritems(its))), rc)))
    case Lex.Bad{}:
      Unit

# the lexer's state as lexemes read and what is read since
def jl(st: Lex.Lex, +rc: List<&2, Char>) -> Type:
  match st:
    case Lex.Lex{md, buf, toks}:
      jm(md, buf, toks, rc)

# jl through one character from mode Lex.Idle
law j_idle:
  for cls: Lex.Class
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for +e: {Lex.classify(ch) == cls : Lex.Class}
  for h: jl(Lex.Lex{Lex.Idle{}, bf, tk}, rc)
  jl(Lex.step(Lex.Idle{}, cls, ch, bf, tk), ch <> rc)

def j_idle(cls, ch, _bf, tk, rc, e, h):
  match cls:
    case Lex.CPunct{+tt}:
      (+its, (+rws, ((etk, (hok, hws)), erc))) = h
      (M6.It{rws, M6.LP{ch}} <> its, ([], ((Equal.trans(List<&2, Lex.Tok>, tt <> tk, M13.ptok(ch) <> tk,
          M13.ptok(ch) <> M13.rtoks(its),
        Equal.cong(Lex.Tok, List<&2, Lex.Tok>, zz => zz <> tk, tt, M13.ptok(ch), Equal.sym(Lex.Tok, M13.ptok(ch), tt,
        Equal.cong(Lex.Class, Lex.Tok, zz => M13.ptok.go(zz), Lex.classify(ch), Lex.CPunct{tt}, e))),
            Equal.cong(List<&2,
        Lex.Tok>, List<&2, Lex.Tok>, zz => M13.ptok(ch) <> zz, tk, M13.rtoks(its), etk)), (M6.and2(M13.allws(rws),
            M13.itsok(its), hws,
        hok), {==})), Equal.cong(List<&2, Char>, List<&2, Char>, zz => ch <> zz, rc, List.append(&2, Char, rws,
        ritems(its)), erc))))
    case Lex.CQuote{}:
      (+its, (+rws, (icp, erc))) = h
      (its, (rws, ([], ((icp, ({==}, {==})), Equal.trans(List<&2, Char>, ch <> rc, '"' <> rc, '"' <> List.append(&2,
        Char, rws, ritems(its)), Equal.cong(Char, List<&2, Char>, zz => zz <> rc, ch, '"', chr_of(ch, 34,
            M2.cls_quote(ch,
        e))), Equal.cong(List<&2, Char>, List<&2, Char>, zz => '"' <> zz, rc, List.append(&2, Char, rws, ritems(its)),
        erc))))))
    case Lex.CSpace{}:
      (+its, (+rws, ((etk, (hok, hws)), erc))) = h
      (its, (ch <> rws, ((etk, (hok, M6.and2(D1.is_ws(ch), M13.allws(rws), cls_space(ch, e), hws))), Equal.cong(List<&2,
        Char>, List<&2, Char>, zz => ch <> zz, rc, List.append(&2, Char, rws, ritems(its)), erc))))
    case Lex.CBack{}:
      Unit{}
    case Lex.COther{}:
      (+its, (+rws, (icp, erc))) = h
      (its, (rws, (icp, Equal.cong(List<&2, Char>, List<&2, Char>, zz => ch <> zz, rc, List.append(&2, Char, rws,
        ritems(its)), erc))))

# jl through one character from mode Lex.Word
law j_word:
  for cls: Lex.Class
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for +e: {Lex.classify(ch) == cls : Lex.Class}
  for h: jl(Lex.Lex{Lex.Word{}, bf, tk}, rc)
  jl(Lex.step(Lex.Word{}, cls, ch, bf, tk), ch <> rc)

def j_word(cls, ch, bf, tk, rc, e, h):
  match cls:
    case Lex.CPunct{+tt}:
      (+its, (+rws, ((etk, (hok, hws)), erc))) = h
      (M6.It{[], M6.LP{ch}} <> M6.It{rws, M6.LW{Lex.text(bf)}} <> its, ([], ((Equal.trans(List<&2, Lex.Tok>,
        tt <> Lex.TWord{Lex.text(bf)} <> tk, M13.ptok(ch) <> Lex.TWord{Lex.text(bf)} <> tk,
        M13.ptok(ch) <> Lex.TWord{Lex.text(bf)} <> M13.rtoks(its), Equal.cong(Lex.Tok, List<&2, Lex.Tok>,
        zz => zz <> Lex.TWord{Lex.text(bf)} <> tk, tt, M13.ptok(ch), Equal.sym(Lex.Tok, M13.ptok(ch), tt,
            Equal.cong(Lex.Class,
        Lex.Tok, zz => M13.ptok.go(zz), Lex.classify(ch), Lex.CPunct{tt}, e))), Equal.cong(List<&2, Lex.Tok>, List<&2,
        Lex.Tok>, zz => M13.ptok(ch) <> Lex.TWord{Lex.text(bf)} <> zz, tk, M13.rtoks(its), etk)),
            (M6.and2(M13.allws(rws), M13.itsok(its),
        hws, hok), {==})), Equal.trans(List<&2, Char>, ch <> rc, ch <> List.append(&2, Char, bf, List.append(&2, Char,
        rws, ritems(its))), ch <> List.reverse.go(&2, Char, String.to_list(Lex.text(bf)), List.append(&2, Char, rws,
        ritems(its))), Equal.cong(List<&2, Char>, List<&2, Char>, zz => ch <> zz, rc, List.append(&2, Char, bf,
        List.append(&2, Char, rws, ritems(its))), erc), Equal.cong(List<&2, Char>, List<&2, Char>, zz => ch <> zz,
        List.append(&2, Char, bf, List.append(&2, Char, rws, ritems(its))), List.reverse.go(&2, Char,
        String.to_list(Lex.text(bf)), List.append(&2, Char, rws, ritems(its))), Equal.sym(List<&2, Char>,
        List.reverse.go(&2, Char, String.to_list(Lex.text(bf)), List.append(&2, Char, rws, ritems(its))),
        List.append(&2, Char, bf, List.append(&2, Char, rws, ritems(its))), text_rc(bf, "", List.append(&2, Char, rws,
        ritems(its)))))))))
    case Lex.CQuote{}:
      (+its, (+rws, ((etk, (hok, hws)), erc))) = h
      (M6.It{rws, M6.LW{Lex.text(bf)}} <> its, ([], ([], (((Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TWord{Lex.text(bf)} <> zz, tk, M13.rtoks(its), etk), (M6.and2(M13.allws(rws), M13.itsok(its), hws,
            hok),
        {==})), ({==}, {==})), Equal.trans(List<&2, Char>, ch <> rc, '"' <> rc, '"' <> List.reverse.go(&2, Char,
          String.to_list(Lex.text(bf)), List.append(&2, Char, rws, ritems(its))), Equal.cong(Char, List<&2, Char>,
          zz => zz <> rc, ch, '"', chr_of(ch, 34, M2.cls_quote(ch, e))), Equal.trans(List<&2, Char>, '"' <> rc,
          '"' <> List.append(&2, Char, bf, List.append(&2, Char, rws, ritems(its))), '"' <> List.reverse.go(&2, Char,
          String.to_list(Lex.text(bf)), List.append(&2, Char, rws, ritems(its))), Equal.cong(List<&2, Char>, List<&2,
          Char>, zz => '"' <> zz, rc, List.append(&2, Char, bf, List.append(&2, Char, rws, ritems(its))), erc),
          Equal.cong(List<&2, Char>, List<&2, Char>, zz => '"' <> zz, List.append(&2, Char, bf, List.append(&2, Char,
          rws, ritems(its))), List.reverse.go(&2, Char, String.to_list(Lex.text(bf)), List.append(&2, Char, rws,
          ritems(its))), Equal.sym(List<&2, Char>, List.reverse.go(&2, Char, String.to_list(Lex.text(bf)),
          List.append(&2, Char, rws, ritems(its))), List.append(&2, Char, bf, List.append(&2, Char, rws, ritems(its))),
          text_rc(bf, "", List.append(&2, Char, rws, ritems(its)))))))))))
    case Lex.CSpace{}:
      (+its, (+rws, ((etk, (hok, hws)), erc))) = h
      (M6.It{rws, M6.LW{Lex.text(bf)}} <> its, ([ch], ((Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TWord{Lex.text(bf)} <> zz, tk, M13.rtoks(its), etk), (M6.and2(M13.allws(rws), M13.itsok(its), hws,
            hok),
        M6.and2(D1.is_ws(ch), M13.allws([]), cls_space(ch, e), {==}))), Equal.trans(List<&2, Char>, ch <> rc,
          ch <> List.append(&2, Char, bf, List.append(&2, Char, rws, ritems(its))), ch <> List.reverse.go(&2, Char,
          String.to_list(Lex.text(bf)), List.append(&2, Char, rws, ritems(its))), Equal.cong(List<&2, Char>, List<&2,
          Char>, zz => ch <> zz, rc, List.append(&2, Char, bf, List.append(&2, Char, rws, ritems(its))), erc),
          Equal.cong(List<&2, Char>, List<&2, Char>, zz => ch <> zz, List.append(&2, Char, bf, List.append(&2, Char,
          rws, ritems(its))), List.reverse.go(&2, Char, String.to_list(Lex.text(bf)), List.append(&2, Char, rws,
          ritems(its))), Equal.sym(List<&2, Char>, List.reverse.go(&2, Char, String.to_list(Lex.text(bf)),
          List.append(&2, Char, rws, ritems(its))), List.append(&2, Char, bf, List.append(&2, Char, rws, ritems(its))),
          text_rc(bf, "", List.append(&2, Char, rws, ritems(its)))))))))
    case Lex.CBack{}:
      Unit{}
    case Lex.COther{}:
      (+its, (+rws, (icp, erc))) = h
      (its, (rws, (icp, Equal.cong(List<&2, Char>, List<&2, Char>, zz => ch <> zz, rc, List.append(&2, Char, bf,
        List.append(&2, Char, rws, ritems(its))), erc))))

# jl through a character a string keeps, once whether it is a control is named
law j_raw:
  for b: Bool
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for cls: Lex.Class
  for e: {Lex.classify(ch) == cls : Lex.Class}
  for hq: {notqb(cls) == True{} : Bool}
  for hlt: {U32.is_lt(Char.to_u32(ch), 32) == b : Bool}
  for h: jl(Lex.Lex{Lex.Str{}, bf, tk}, rc)
  jl(Lex.step.str.go(ch, bf, tk, b), ch <> rc)

def j_raw(b, ch, bf, _tk, rc, cls, e, hq, hlt, h):
  match b:
    case True{}:
      Unit{}
    case False{}:
      (+its, (+rws, (+ps, ((icp, (ebf, hps)), erc)))) = h
      (its, (rws, (D2.PRaw{ch} <> ps, ((icp, (Equal.cong(List<&2, Char>, List<&2, Char>, zz => ch <> zz, bf,
        M13.pchars(ps), ebf), M6.and2(D1.raw_char(ch),
        D2.spell_ok(ps), rawc(ch, cls, e, hq, hlt), hps))), Equal.cong(List<&2, Char>, List<&2, Char>,
          zz => ch <> zz, rc, rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))), erc)))))

# jl through one character from mode Lex.Str
law j_str:
  for cls: Lex.Class
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for +e: {Lex.classify(ch) == cls : Lex.Class}
  for h: jl(Lex.Lex{Lex.Str{}, bf, tk}, rc)
  jl(Lex.step(Lex.Str{}, cls, ch, bf, tk), ch <> rc)

def j_str(cls, ch, bf, tk, rc, e, h):
  match cls:
    case Lex.CQuote{}:
      (+its, (+rws, (+ps, (((etk, (hok, hws)), (ebf, hps)), erc)))) = h
      (M6.It{rws, M6.LS{List.reverse.go(&2, D2.Piece, ps, [])}} <> its, ([], ((Equal.trans(List<&2, Lex.Tok>,
        Lex.TStr{Lex.text(bf)} <> tk, Lex.TStr{D2.spelled(List.reverse.go(&2, D2.Piece, ps, []))} <> tk,
        Lex.TStr{D2.spelled(List.reverse.go(&2, D2.Piece, ps, []))} <> M13.rtoks(its), Equal.cong(String, List<&2,
        Lex.Tok>, zz => Lex.TStr{zz} <> tk, Lex.text(bf), D2.spelled(List.reverse.go(&2, D2.Piece, ps, [])),
        Equal.trans(String, Lex.text.go(bf, ""), Lex.text.go(M13.pchars(ps), ""), D2.spelled(List.reverse.go(&2,
        D2.Piece, ps, [])), Equal.cong(List<&2, Char>, String, zz => Lex.text.go(zz, ""), bf, M13.pchars(ps), ebf),
        text_pc(ps, []))), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{D2.spelled(List.reverse.go(&2, D2.Piece, ps, []))} <> zz, tk, M13.rtoks(its), etk)),
        (M6.and2(M13.allws(rws), Bool.and(D2.spell_ok(List.reverse.go(&2, D2.Piece, ps, [])), M13.itsok(its)), hws,
        M6.and2(D2.spell_ok(List.reverse.go(&2, D2.Piece, ps, [])), M13.itsok(its), spell_ok_rev(ps, [], hps, {==}),
          hok)), {==})), Equal.trans(List<&2, Char>, ch <> rc, '"' <> rc, '"' <> List.reverse.go(&2, Char,
          String.to_list(D2.spell(List.reverse.go(&2, D2.Piece, ps, []))), '"' <> List.append(&2, Char, rws,
          ritems(its))), Equal.cong(Char, List<&2, Char>, zz => zz <> rc, ch, '"', chr_of(ch, 34, M2.cls_quote(ch, e))),
          Equal.trans(List<&2, Char>, '"' <> rc, '"' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))),
          '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(List.reverse.go(&2, D2.Piece, ps, []))),
          '"' <> List.append(&2, Char, rws, ritems(its))), Equal.cong(List<&2, Char>, List<&2, Char>, zz => '"' <> zz,
          rc, rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))), erc), Equal.cong(List<&2, Char>, List<&2, Char>,
          zz => '"' <> zz, rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))), List.reverse.go(&2, Char,
          String.to_list(D2.spell(List.reverse.go(&2, D2.Piece, ps, []))), '"' <> List.append(&2, Char, rws,
          ritems(its))), Equal.sym(List<&2, Char>, List.reverse.go(&2, Char,
          String.to_list(D2.spell(List.reverse.go(&2, D2.Piece, ps, []))), '"' <> List.append(&2, Char, rws,
          ritems(its))), rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))), spell_rev(ps, [],
          '"' <> List.append(&2, Char, rws, ritems(its))))))))))
    case Lex.CBack{}:
      (+its, (+rws, (+ps, (scp, erc)))) = h
      (its, (rws, (ps, (scp, Equal.trans(List<&2, Char>, ch <> rc, '\\' <> rc, '\\' <> rsp(ps, '"' <> List.append(&2,
        Char, rws, ritems(its))), Equal.cong(Char, List<&2, Char>, zz => zz <> rc, ch, '\\', chr_of(ch, 92,
        M2.cls_back(ch, e))), Equal.cong(List<&2, Char>, List<&2, Char>, zz => '\\' <> zz, rc, rsp(ps,
        '"' <> List.append(&2, Char, rws, ritems(its))), erc))))))
    case Lex.CPunct{+tt}:
      j_raw(U32.is_lt(Char.to_u32(ch), 32), ch, bf, tk, rc, Lex.CPunct{tt}, e, {==}, {==}, h)
    case Lex.CSpace{}:
      j_raw(U32.is_lt(Char.to_u32(ch), 32), ch, bf, tk, rc, Lex.CSpace{}, e, {==}, {==}, h)
    case Lex.COther{}:
      j_raw(U32.is_lt(Char.to_u32(ch), 32), ch, bf, tk, rc, Lex.COther{}, e, {==}, {==}, h)

# jl through the character after a backslash that is not u, by what it stands for
law j_eput:
  for mb: Maybe<&2, Char>
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for +em: {Lex.unescape(ch) == mb : Maybe<&2, Char>}
  for h: jl(Lex.Lex{Lex.Esc{}, bf, tk}, rc)
  jl(Lex.escape.put(mb, bf, tk), ch <> rc)

def j_eput(mb, ch, bf, _tk, rc, em, h):
  match mb:
    case Some{+c2}:
      (+its, (+rws, (+ps, ((icp, (ebf, hps)), erc)))) = h
      (its, (rws, (D2.PEsc{ch} <> ps, ((icp, (Equal.trans(List<&2, Char>, c2 <> bf, c2 <> M13.pchars(ps),
        D2.some_or(D2.unesc(ch), ch) <> M13.pchars(ps), Equal.cong(List<&2, Char>, List<&2, Char>, zz => c2 <> zz, bf,
        M13.pchars(ps), ebf), Equal.cong(Char, List<&2, Char>, zz => zz <> M13.pchars(ps), c2, D2.some_or(D2.unesc(ch),
        ch), Equal.sym(Char, D2.some_or(D2.unesc(ch), ch), c2, Equal.cong(Maybe<&2, Char>, Char,
        zz => D2.some_or(zz, ch), D2.unesc(ch), Some{c2}, em)))), M6.and2(D2.has_char(D2.unesc(ch)),
        D2.spell_ok(ps),
        Equal.cong(Maybe<&2, Char>, Bool, zz => D2.has_char(zz), D2.unesc(ch), Some{c2}, em), hps))),
        Equal.cong(List<&2, Char>, List<&2, Char>, zz => ch <> zz, rc, '\\' <> rsp(ps, '"' <> List.append(&2, Char,
          rws, ritems(its))), erc)))))
    case None{}:
      Unit{}

# jl through the character after a backslash, once whether it is u is named
law j_esc:
  for b: Bool
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for eu: {U32.is_eq(Char.to_u32(ch), 117) == b : Bool}
  for h: jl(Lex.Lex{Lex.Esc{}, bf, tk}, rc)
  jl(Lex.escape.go(ch, bf, tk, b), ch <> rc)

def j_esc(b, ch, bf, tk, rc, eu, h):
  match b:
    case True{}:
      (+its, (+rws, (+ps, (scp, erc)))) = h
      (its, (rws, (ps, (scp, ({==}, Equal.trans(List<&2, Char>, ch <> rc, 'u' <> rc, 'u' <> '\\' <> rsp(ps,
        '"' <> List.append(&2, Char, rws, ritems(its))), Equal.cong(Char, List<&2, Char>, zz => zz <> rc, ch, 'u',
        chr_of(ch, 117, M13.ueq(Char.to_u32(ch), 117, eu))), Equal.cong(List<&2, Char>, List<&2, Char>, zz => 'u' <> zz,
        rc, '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))), erc)))))))
    case False{}:
      j_eput(Lex.unescape(ch), ch, bf, tk, rc, {==}, h)

# jl through the character after a high surrogate's escape, once whether it is
# a backslash is named
law j_hi:
  for b: Bool
  for +hi: U32
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for eb: {U32.is_eq(Char.to_u32(ch), 92) == b : Bool}
  for h: jl(Lex.Lex{Lex.Hi{hi}, bf, tk}, rc)
  jl(Lex.step.hi.go(hi, bf, tk, b), ch <> rc)

def j_hi(b, _hi, ch, _bf, _tk, rc, eb, h):
  match b:
    case True{}:
      (+its, (+rws, (+ps, (+h1, (+h2, (+h3, (+h4, (scp, (hjp, erc))))))))) = h
      (its, (rws, (ps, (h1, (h2, (h3, (h4, (scp, (hjp, Equal.trans(List<&2, Char>, ch <> rc, '\\' <> rc,
        '\\' <> h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))),
        Equal.cong(Char, List<&2, Char>, zz => zz <> rc, ch, '\\', chr_of(ch, 92, M13.ueq(Char.to_u32(ch), 92, eb))),
        Equal.cong(List<&2, Char>, List<&2, Char>, zz => '\\' <> zz, rc, h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps,
        '"' <> List.append(&2, Char, rws, ritems(its))), erc)))))))))))
    case False{}:
      Unit{}

# jl through the character after a high surrogate's escape and a backslash,
# once whether it is u is named
law j_hiesc:
  for b: Bool
  for +hi: U32
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for eb: {U32.is_eq(Char.to_u32(ch), 117) == b : Bool}
  for h: jl(Lex.Lex{Lex.HiEsc{hi}, bf, tk}, rc)
  jl(Lex.step.hiesc.go(hi, bf, tk, b), ch <> rc)

def j_hiesc(b, _hi, ch, _bf, _tk, rc, eb, h):
  match b:
    case True{}:
      (+its, (+rws, (+ps, (+h1, (+h2, (+h3, (+h4, (scp, (hjp, erc))))))))) = h
      (its, (rws, (ps, (h1, (h2, (h3, (h4, (scp, (hjp, ({==}, Equal.trans(List<&2, Char>, ch <> rc, 'u' <> rc,
        'u' <> '\\' <> h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))),
        Equal.cong(Char, List<&2, Char>, zz => zz <> rc, ch, 'u', chr_of(ch, 117, M13.ueq(Char.to_u32(ch), 117, eb))),
        Equal.cong(List<&2, Char>, List<&2, Char>, zz => 'u' <> zz, rc,
        '\\' <> h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))),
        erc))))))))))))
    case False{}:
      Unit{}

# jl through a \u escape's four digits and the code point they spell, by what
# kind of code point it is
law j_uend:
  for key: Lex.Sur
  for +d1: Char
  for +d2: Char
  for +d3: Char
  for +d4: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for +its: List<&2, M6.It>
  for +rws: List<&2, Char>
  for +ps: List<&2, D2.Piece>
  for ek: {Lex.unicode.sur(D2.hex4(d1, d2, d3, d4)) == key : Lex.Sur}
  for hd1: {D2.hexd(d1) == True{} : Bool}
  for hd2: {D2.hexd(d2) == True{} : Bool}
  for hd3: {D2.hexd(d3) == True{} : Bool}
  for hd4: {D2.hexd(d4) == True{} : Bool}
  for scp: M13.sc(its, rws, ps, bf, tk)
  for erc: {rc == d3 <> d2 <> d1 <> 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))) : List<&2,
    Char>}
  jl(Lex.unicode.end.go(D2.hex4(d1, d2, d3, d4), bf, tk, key), d4 <> rc)

def j_uend(key, d1, d2, d3, d4, bf, _tk, rc, its, rws, ps, ek, hd1, hd2, hd3, hd4, scp, erc):
  match key:
    case Lex.SOk{}:
      (icp, (ebf, hps)) = scp
      (its, (rws, (D2.PU{d1, d2, d3, d4} <> ps, ((icp, (Equal.cong(List<&2, Char>, List<&2, Char>,
        zz => Char.from_u32(D2.hex4(d1, d2, d3, d4)) <> zz, bf, M13.pchars(ps), ebf),
        M6.and2(D2.piece.ok(D2.PU{d1, d2, d3, d4}), D2.spell_ok(ps), M6.and2(Bool.and(D2.hexd(d1),
          Bool.and(D2.hexd(d2), Bool.and(D2.hexd(d3), D2.hexd(d4)))), D2.non_sur(D2.hex4(d1, d2, d3, d4)),
        M6.and2(D2.hexd(d1), Bool.and(D2.hexd(d2), Bool.and(D2.hexd(d3), D2.hexd(d4))), hd1, M6.and2(D2.hexd(d2),
          Bool.and(D2.hexd(d3), D2.hexd(d4)), hd2, M6.and2(D2.hexd(d3), D2.hexd(d4), hd3, hd4))),
          sur_inv(D2.hex4(d1, d2, d3, d4), Lex.SOk{}, ek)), hps))),
        Equal.cong(List<&2, Char>, List<&2, Char>, zz => d4 <> zz, rc, d3 <> d2 <> d1 <> 'u' <> '\\' <> rsp(ps,
          '"' <> List.append(&2, Char, rws, ritems(its))), erc)))))
    case Lex.SHi{}:
      (its, (rws, (ps, (d1, (d2, (d3, (d4, (scp, ((hd1, (hd2, (hd3, (hd4, ({==}, sur_inv(D2.hex4(d1, d2, d3, d4),
        Lex.SHi{}, ek)))))), Equal.cong(List<&2, Char>, List<&2, Char>, zz => d4 <> zz, rc,
        d3 <> d2 <> d1 <> 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))), erc))))))))))
    case Lex.SLo{}:
      Unit{}

# jl through one hex digit of a \u escape, by how many are left
law j_uput:
  for left: Nat
  for +acc: U32
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for +its: List<&2, M6.It>
  for +rws: List<&2, Char>
  for +ps: List<&2, D2.Piece>
  for +eh: {Lex.hex.ok(Char.to_u32(ch)) == True{} : Bool}
  for scp: M13.sc(its, rws, ps, bf, tk)
  for uh: uj(left, acc, 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))), rc)
  jl(Lex.unicode.put(left, acc, Lex.hex(ch), bf, tk), ch <> rc)

def j_uput(left, acc, ch, bf, tk, rc, its, rws, ps, eh, scp, uh):
  match left:
    case 0n:
      (+d1, (+d2, (+d3, (hd1, (hd2, (hd3, (ea, erc))))))) = uh
      ea2 = Equal.sym(U32, acc, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, d1), d2), d3), ea)
      %ea2 : jl(Lex.unicode.end(U32.add(U32.mul(_, 16), Lex.hex(ch)), bf, tk), ch <> rc)
      j_uend(Lex.unicode.sur(D2.hex4(d1, d2, d3, ch)), d1, d2, d3, ch, bf, tk, rc, its, rws, ps, {==}, hd1, hd2, hd3,
        eh, scp, erc)
    case 1n+l1:
      match l1:
        case 0n:
          (+d1, (+d2, (hd1, (hd2, (ea, erc))))) = uh
          (its, (rws, (ps, (scp, (d1, (d2, (ch, (hd1, (hd2, (eh, (Equal.cong(U32, U32, zz => U32.add(U32.mul(zz, 16),
            Lex.hex(ch)), acc, D2.hex.acc(D2.hex.acc(0, d1), d2), ea), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => ch <> zz, rc, d2 <> d1 <> 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))),
            erc))))))))))))
        case 1n+l2:
          match l2:
            case 0n:
              (+d1, (hd1, (ea, erc))) = uh
              (its, (rws, (ps, (scp, (d1, (ch, (hd1, (eh, (Equal.cong(U32, U32, zz => U32.add(U32.mul(zz, 16),
                Lex.hex(ch)), acc, D2.hex.acc(0, d1), ea), Equal.cong(List<&2, Char>, List<&2, Char>, zz => ch <> zz,
                rc, d1 <> 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws, ritems(its))), erc))))))))))
            case 1n+l3:
              match l3:
                case 0n:
                  (ea, erc) = uh
                  (its, (rws, (ps, (scp, (ch, (eh, (Equal.cong(U32, U32, zz => U32.add(U32.mul(zz, 16), Lex.hex(ch)),
                    acc, 0, ea), Equal.cong(List<&2, Char>, List<&2, Char>, zz => ch <> zz, rc, 'u' <> '\\' <> rsp(ps,
                    '"' <> List.append(&2, Char, rws, ritems(its))), erc))))))))
                case 1n+_l4:
                  match uh:

# jl through a character of a \u escape, once whether it is a hex digit is named
law j_uni:
  for b: Bool
  for left: Nat
  for +acc: U32
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for +eh: {Lex.hex.ok(Char.to_u32(ch)) == b : Bool}
  for h: jl(Lex.Lex{Lex.Uni{left, acc}, bf, tk}, rc)
  jl(Lex.unicode.go(left, acc, ch, bf, tk, b), ch <> rc)

def j_uni(b, left, acc, ch, bf, tk, rc, eh, h):
  match b:
    case True{}:
      (+its, (+rws, (+ps, (scp, uh)))) = h
      j_uput(left, acc, ch, bf, tk, rc, its, rws, ps, eh, scp, uh)
    case False{}:
      Unit{}

# jl through a low surrogate's \u escape's four digits and the code point they
# spell, by what kind of code point it is
law j_lend:
  for key: Lex.Sur
  for +d1: Char
  for +d2: Char
  for +d3: Char
  for +d4: Char
  for +hi: U32
  for +h1: Char
  for +h2: Char
  for +h3: Char
  for +h4: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for +its: List<&2, M6.It>
  for +rws: List<&2, Char>
  for +ps: List<&2, D2.Piece>
  for ek: {Lex.unicode.sur(D2.hex4(d1, d2, d3, d4)) == key : Lex.Sur}
  for hd1: {D2.hexd(d1) == True{} : Bool}
  for hd2: {D2.hexd(d2) == True{} : Bool}
  for hd3: {D2.hexd(d3) == True{} : Bool}
  for hd4: {D2.hexd(d4) == True{} : Bool}
  for scp: M13.sc(its, rws, ps, bf, tk)
  for hjp: hj(hi, h1, h2, h3, h4)
  for erc: {rc == d3 <> d2 <> d1 <> 'u' <> '\\' <> h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps,
    '"' <> List.append(&2, Char, rws, ritems(its))) : List<&2, Char>}
  jl(Lex.unicode.low.end.go(D2.hex4(d1, d2, d3, d4), hi, bf, tk, key), d4 <> rc)

def j_lend(key, d1, d2, d3, d4, hi, h1, h2, h3, h4, bf, _tk, rc, its, rws, ps, ek, hd1, hd2, hd3, hd4, scp, hjp, erc):
  match key:
    case Lex.SLo{}:
      (icp, (ebf, hps)) = scp
      (hh1, (hh2, (hh3, (hh4, (+ehi, hin))))) = hjp
      (its, (rws, (D2.PPair{h1, h2, h3, h4, d1, d2, d3, d4} <> ps, ((icp, (Equal.trans(List<&2, Char>,
        Char.from_u32(Lex.unicode.pair(hi, D2.hex4(d1, d2, d3, d4))) <> bf, Char.from_u32(Lex.unicode.pair(hi,
        D2.hex4(d1, d2, d3, d4))) <> M13.pchars(ps), Char.from_u32(Lex.unicode.pair(D2.hex4(h1, h2, h3, h4),
        D2.hex4(d1, d2, d3, d4))) <> M13.pchars(ps), Equal.cong(List<&2, Char>, List<&2, Char>,
        zz => Char.from_u32(Lex.unicode.pair(hi, D2.hex4(d1, d2, d3, d4))) <> zz, bf, M13.pchars(ps), ebf),
        Equal.cong(U32, List<&2, Char>, zz => Char.from_u32(Lex.unicode.pair(zz, D2.hex4(d1, d2, d3,
        d4))) <> M13.pchars(ps), hi, D2.hex4(h1, h2, h3, h4), ehi)), M6.and2(D2.piece.ok(D2.PPair{h1, h2, h3, h4, d1,
        d2, d3, d4}), D2.spell_ok(ps), M6.and2(Bool.and(D2.hexd(h1), Bool.and(D2.hexd(h2), Bool.and(D2.hexd(h3),
        D2.hexd(h4)))), Bool.and(Bool.and(D2.hexd(d1), Bool.and(D2.hexd(d2), Bool.and(D2.hexd(d3),
        D2.hexd(d4)))), Bool.and(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(d1, d2, d3, d4)))),
        M6.and2(D2.hexd(h1), Bool.and(D2.hexd(h2), Bool.and(D2.hexd(h3), D2.hexd(h4))), hh1, M6.and2(D2.hexd(h2),
        Bool.and(D2.hexd(h3), D2.hexd(h4)), hh2, M6.and2(D2.hexd(h3), D2.hexd(h4), hh3, hh4))),
        M6.and2(Bool.and(D2.hexd(d1), Bool.and(D2.hexd(d2), Bool.and(D2.hexd(d3), D2.hexd(d4)))),
        Bool.and(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(d1, d2, d3, d4))), M6.and2(D2.hexd(d1),
        Bool.and(D2.hexd(d2), Bool.and(D2.hexd(d3), D2.hexd(d4))), hd1, M6.and2(D2.hexd(d2),
        Bool.and(D2.hexd(d3), D2.hexd(d4)), hd2, M6.and2(D2.hexd(d3), D2.hexd(d4), hd3, hd4))),
        M6.and2(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(d1, d2, d3, d4)), Equal.trans(Bool,
        D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.in_hi(hi), True{}, Equal.cong(U32, Bool, zz => D2.in_hi(zz),
        D2.hex4(h1, h2, h3, h4), hi, Equal.sym(U32, hi, D2.hex4(h1, h2, h3, h4), ehi)), hin), sur_inv(D2.hex4(d1,
        d2, d3, d4), Lex.SLo{}, ek)))), hps))),
        Equal.cong(List<&2, Char>, List<&2, Char>, zz => d4 <> zz, rc,
          d3 <> d2 <> d1 <> 'u' <> '\\' <> h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char,
          rws, ritems(its))), erc)))))
    case Lex.SOk{}:
      Unit{}
    case Lex.SHi{}:
      Unit{}

# jl through one hex digit of a low surrogate's \u escape, by how many are left
law j_lput:
  for left: Nat
  for +acc: U32
  for +hi: U32
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for +its: List<&2, M6.It>
  for +rws: List<&2, Char>
  for +ps: List<&2, D2.Piece>
  for +h1: Char
  for +h2: Char
  for +h3: Char
  for +h4: Char
  for +eh: {Lex.hex.ok(Char.to_u32(ch)) == True{} : Bool}
  for scp: M13.sc(its, rws, ps, bf, tk)
  for hjp: hj(hi, h1, h2, h3, h4)
  for uh: uj(left, acc, 'u' <> '\\' <> h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws,
    ritems(its))), rc)
  jl(Lex.unicode.low.put(left, acc, hi, Lex.hex(ch), bf, tk), ch <> rc)

def j_lput(left, acc, hi, ch, bf, tk, rc, its, rws, ps, h1, h2, h3, h4, eh, scp, hjp, uh):
  match left:
    case 0n:
      (+d1, (+d2, (+d3, (hd1, (hd2, (hd3, (ea, erc))))))) = uh
      ea2 = Equal.sym(U32, acc, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, d1), d2), d3), ea)
      %ea2 : jl(Lex.unicode.low.end(U32.add(U32.mul(_, 16), Lex.hex(ch)), hi, bf, tk), ch <> rc)
      j_lend(Lex.unicode.sur(D2.hex4(d1, d2, d3, ch)), d1, d2, d3, ch, hi, h1, h2, h3, h4, bf, tk, rc, its, rws, ps,
        {==}, hd1, hd2, hd3, eh, scp, hjp, erc)
    case 1n+l1:
      match l1:
        case 0n:
          (+d1, (+d2, (hd1, (hd2, (ea, erc))))) = uh
          (its, (rws, (ps, (h1, (h2, (h3, (h4, (scp, (hjp, (d1, (d2, (ch, (hd1, (hd2, (eh, (Equal.cong(U32, U32,
            zz => U32.add(U32.mul(zz, 16), Lex.hex(ch)), acc, D2.hex.acc(D2.hex.acc(0, d1), d2), ea),
            Equal.cong(List<&2, Char>, List<&2, Char>, zz => ch <> zz, rc,
            d2 <> d1 <> 'u' <> '\\' <> h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps, '"' <> List.append(&2, Char, rws,
            ritems(its))), erc)))))))))))))))))
        case 1n+l2:
          match l2:
            case 0n:
              (+d1, (hd1, (ea, erc))) = uh
              (its, (rws, (ps, (h1, (h2, (h3, (h4, (scp, (hjp, (d1, (ch, (hd1, (eh, (Equal.cong(U32, U32,
                zz => U32.add(U32.mul(zz, 16), Lex.hex(ch)), acc, D2.hex.acc(0, d1), ea), Equal.cong(List<&2, Char>,
                List<&2, Char>, zz => ch <> zz, rc, d1 <> 'u' <> '\\' <> h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps,
                '"' <> List.append(&2, Char, rws, ritems(its))), erc)))))))))))))))
            case 1n+l3:
              match l3:
                case 0n:
                  (ea, erc) = uh
                  (its, (rws, (ps, (h1, (h2, (h3, (h4, (scp, (hjp, (ch, (eh, (Equal.cong(U32, U32,
                    zz => U32.add(U32.mul(zz, 16), Lex.hex(ch)), acc, 0, ea), Equal.cong(List<&2, Char>, List<&2,
                    Char>, zz => ch <> zz, rc, 'u' <> '\\' <> h4 <> h3 <> h2 <> h1 <> 'u' <> '\\' <> rsp(ps,
                    '"' <> List.append(&2, Char, rws, ritems(its))), erc)))))))))))))
                case 1n+_l4:
                  match uh:

# jl through a character of a low surrogate's \u escape, once whether it is a
# hex digit is named
law j_lo:
  for b: Bool
  for left: Nat
  for +acc: U32
  for +hi: U32
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for +eh: {Lex.hex.ok(Char.to_u32(ch)) == b : Bool}
  for h: jl(Lex.Lex{Lex.Lo{left, acc, hi}, bf, tk}, rc)
  jl(Lex.unicode.low.go(left, acc, hi, ch, bf, tk, b), ch <> rc)

def j_lo(b, left, acc, hi, ch, bf, tk, rc, eh, h):
  match b:
    case True{}:
      (+its, (+rws, (+ps, (+h1, (+h2, (+h3, (+h4, (scp, (hjp, uh))))))))) = h
      j_lput(left, acc, hi, ch, bf, tk, rc, its, rws, ps, h1, h2, h3, h4, eh, scp, hjp, uh)
    case False{}:
      Unit{}

# jl through one character, by the lexer's mode
law jm_step:
  for md: Lex.Mode
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +ch: Char
  for +rc: List<&2, Char>
  for h: jl(Lex.Lex{md, bf, tk}, rc)
  jl(Lex.feed(ch, Lex.Lex{md, bf, tk}), ch <> rc)

def jm_step(md, bf, tk, ch, rc, h):
  match md:
    case Lex.Idle{}:
      j_idle(Lex.classify(ch), ch, bf, tk, rc, {==}, h)
    case Lex.Word{}:
      j_word(Lex.classify(ch), ch, bf, tk, rc, {==}, h)
    case Lex.Str{}:
      j_str(Lex.classify(ch), ch, bf, tk, rc, {==}, h)
    case Lex.Esc{}:
      j_esc(U32.is_eq(Char.to_u32(ch), 117), ch, bf, tk, rc, {==}, h)
    case Lex.Uni{left, +acc}:
      j_uni(Lex.hex.ok(Char.to_u32(ch)), left, acc, ch, bf, tk, rc, {==}, h)
    case Lex.Hi{+hi}:
      j_hi(U32.is_eq(Char.to_u32(ch), 92), hi, ch, bf, tk, rc, {==}, h)
    case Lex.HiEsc{+hi}:
      j_hiesc(U32.is_eq(Char.to_u32(ch), 117), hi, ch, bf, tk, rc, {==}, h)
    case Lex.Lo{left, +acc, +hi}:
      j_lo(Lex.hex.ok(Char.to_u32(ch)), left, acc, hi, ch, bf, tk, rc, {==}, h)
    case Lex.Bad{}:
      Unit{}

# jl through one character
law jstep:
  for st: Lex.Lex
  for +ch: Char
  for +rc: List<&2, Char>
  for h: jl(st, rc)
  jl(Lex.feed(ch, st), ch <> rc)

def jstep(st, ch, rc, h):
  match st:
    case Lex.Lex{md, +bf, +tk}:
      jm_step(md, bf, tk, ch, rc, h)

# jl through every character
law jrun:
  for cs: List<&2, Char>
  for +st: Lex.Lex
  for +rc: List<&2, Char>
  for h: jl(st, rc)
  jl(Lex.run(cs, st), List.reverse.go(&2, Char, cs, rc))

def jrun(cs, st, rc, h):
  match cs:
    case Nil{}:
      h
    case +ch <> +tl:
      jrun(tl, Lex.feed(ch, st), ch <> rc, jstep(st, ch, rc, h))

# laws/ParsesExactlyJsonTexts.bend: a derivation from lexemes and the value they parse to

# what a punctuation lexeme's token says of its character
def lpg(ch: Char, tt: Lex.Tok) -> Type:
  match tt:
    case Lex.TOpenArr{}:
      {ch == '[' : Char}
    case Lex.TCloseArr{}:
      {ch == ']' : Char}
    case Lex.TOpenObj{}:
      {ch == '{' : Char}
    case Lex.TCloseObj{}:
      {ch == '}' : Char}
    case Lex.TColon{}:
      {ch == ':' : Char}
    case Lex.TComma{}:
      {ch == ',' : Char}
    case Lex.TBad{}:
      Unit
    case _:
      Empty

# past classify's last test
law lp_end:
  for +cp: U32
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Lex.COther{})) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_end(cp, _tt, h):
  %h : lpg(Chr{cp}, _)
  Unit{}

# classify's test for 9, once its answer is named
law lp_11:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 9) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CSpace{}, Lex.COther{}))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_11(cp, bb, _eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Unit{}
    case False{}:
      lp_end(cp, tt, h)

# classify's test for 13, once its answer is named
law lp_10:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 13) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_10(cp, bb, _eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Unit{}
    case False{}:
      lp_11(cp, U32.is_eq(cp, 9), {==}, tt, h)

# classify's test for 10, once its answer is named
law lp_9:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 10) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13),
      Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_9(cp, bb, _eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Unit{}
    case False{}:
      lp_10(cp, U32.is_eq(cp, 13), {==}, tt, h)

# classify's test for 32, once its answer is named
law lp_8:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 32) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10),
      Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})))))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_8(cp, bb, _eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Unit{}
    case False{}:
      lp_9(cp, U32.is_eq(cp, 10), {==}, tt, h)

# classify's test for 92, once its answer is named
law lp_7:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 92) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_7(cp, bb, _eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Unit{}
    case False{}:
      lp_8(cp, U32.is_eq(cp, 32), {==}, tt, h)

# classify's test for 34, once its answer is named
law lp_6:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 34) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})))))))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_6(cp, bb, _eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Unit{}
    case False{}:
      lp_7(cp, U32.is_eq(cp, 92), {==}, tt, h)

# classify's test for 44, once its answer is named
law lp_5:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 44) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34),
    Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32),
    Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13),
    Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))))))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_5(cp, bb, eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Equal.cong(U32, Char, zz => Chr{zz}, cp, 44, M13.ueq(cp, 44, eb))
    case False{}:
      lp_6(cp, U32.is_eq(cp, 34), {==}, tt, h)

# classify's test for 58, once its answer is named
law lp_4:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 58) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
    Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp,
    92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10),
    Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9),
    Lex.CSpace{}, Lex.COther{})))))))))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_4(cp, bb, eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Equal.cong(U32, Char, zz => Chr{zz}, cp, 58, M13.ueq(cp, 58, eb))
    case False{}:
      lp_5(cp, U32.is_eq(cp, 44), {==}, tt, h)

# classify's test for 125, once its answer is named
law lp_3:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 125) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp,
      58),
    Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{}))))))))))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_3(cp, bb, eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Equal.cong(U32, Char, zz => Chr{zz}, cp, 125, M13.ueq(cp, 125, eb))
    case False{}:
      lp_4(cp, U32.is_eq(cp, 58), {==}, tt, h)

# classify's test for 123, once its answer is named
law lp_2:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 123) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp,
      125),
    Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{})))))))))))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_2(cp, bb, eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Equal.cong(U32, Char, zz => Chr{zz}, cp, 123, M13.ueq(cp, 123, eb))
    case False{}:
      lp_3(cp, U32.is_eq(cp, 125), {==}, tt, h)

# classify's test for 93, once its answer is named
law lp_1:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 93) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp,
      123),
    Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}},
    Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
    Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp,
    92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10),
    Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9),
    Lex.CSpace{}, Lex.COther{}))))))))))))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_1(cp, bb, eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Equal.cong(U32, Char, zz => Chr{zz}, cp, 93, M13.ueq(cp, 93, eb))
    case False{}:
      lp_2(cp, U32.is_eq(cp, 123), {==}, tt, h)

# classify's test for 91, once its answer is named
law lp_0:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 91) == bb : Bool}
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok.go(Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp,
      93),
    Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 123), Lex.CPunct{Lex.TOpenObj{}},
    Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58),
    Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class,
    U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})))))))))))))) == tt : Lex.Tok}
  lpg(Chr{cp}, tt)

def lp_0(cp, bb, eb, tt, h):
  match bb:
    case True{}:
      %h : lpg(Chr{cp}, _)
      Equal.cong(U32, Char, zz => Chr{zz}, cp, 91, M13.ueq(cp, 91, eb))
    case False{}:
      lp_1(cp, U32.is_eq(cp, 93), {==}, tt, h)

# a punctuation lexeme's token names its character
law lp_inv:
  for ch: Char
  for tt: Lex.Tok
  for h: {M6.den(M13.ptok(ch)) == tt : Lex.Tok}
  lpg(ch, tt)

def lp_inv(ch, tt, h):
  match ch:
    case Chr{+uu}:
      lp_0(uu, U32.is_eq(uu, 91), {==}, tt, h)

# a token's kind, as a number
def ttag(tt: Lex.Tok) -> U32:
  match tt:
    case Lex.TOpenArr{}:
      1
    case Lex.TCloseArr{}:
      2
    case Lex.TOpenObj{}:
      3
    case Lex.TCloseObj{}:
      4
    case Lex.TColon{}:
      5
    case Lex.TComma{}:
      6
    case Lex.TStr{_}:
      7
    case Lex.TWord{_}:
      8
    case Lex.TStrS{_, _}:
      9
    case Lex.TWordS{_, _}:
      10
    case Lex.TBad{}:
      11

# a word token's text
def twd(tt: Lex.Tok) -> String:
  match tt:
    case Lex.TWord{txt}:
      txt
    case _:
      ""

# a string token's text
def tsd(tt: Lex.Tok) -> String:
  match tt:
    case Lex.TStr{txt}:
      txt
    case _:
      ""

# lexemes listed last first, reversed onto acc
def ra(its: List<&2, M6.It>, acc: List<&2, Char>) -> List<&2, Char>:
  match its:
    case Nil{}:
      acc
    case M6.It{rws, lx} <> rest:
      M6.rlx(lx, List.append(&2, Char, rws, ra(rest, acc)))

# ritems is ra onto nothing
law ritems_ra:
  for +its: List<&2, M6.It>
  {ritems(its) == ra(its, []) : List<&2, Char>}

def ritems_ra(its):
  match its:
    case Nil{}:
      {==}
    case M6.It{+rws, +lx} <> +rest:
      Equal.cong(List<&2, Char>, List<&2, Char>, zz => M6.rlx(lx, List.append(&2, Char, rws, zz)), ritems(rest),
          ra(rest,
        []), ritems_ra(rest))

# lexemes put back in order spell what they spelled
law fr_rev:
  for +its: List<&2, M6.It>
  for +fs: List<&2, M6.It>
  for +acc: List<&2, Char>
  {M6.fr(List.reverse.go(&2, M6.It, its, fs), acc) == M6.fr(fs, ra(its, acc)) : List<&2, Char>}

def fr_rev(its, fs, acc):
  match its:
    case Nil{}:
      {==}
    case M6.It{+rws, +lx} <> +rest:
      fr_rev(rest, M6.It{rws, lx} <> fs, acc)

# lexemes put back in order have their tokens put back in order
law rtoks_rev:
  for +its: List<&2, M6.It>
  for +fs: List<&2, M6.It>
  {M13.rtoks(List.reverse.go(&2, M6.It, its, fs)) == List.reverse.go(&2, Lex.Tok, M13.rtoks(its),
      M13.rtoks(fs)) : List<&2, Lex.Tok>}

def rtoks_rev(its, fs):
  match its:
    case Nil{}:
      {==}
    case M6.It{+rws, +lx} <> +rest:
      rtoks_rev(rest, M6.It{rws, lx} <> fs)

# lexemes put back in order stay well spelled
law itsok_rev:
  for +its: List<&2, M6.It>
  for +fs: List<&2, M6.It>
  for +hi: {M13.itsok(its) == True{} : Bool}
  for hf: {M13.itsok(fs) == True{} : Bool}
  {M13.itsok(List.reverse.go(&2, M6.It, its, fs)) == True{} : Bool}

def itsok_rev(its, fs, hi, hf):
  match its:
    case Nil{}:
      hf
    case M6.It{+rws, +lx} <> +rest:
      itsok_rev(rest, M6.It{rws, lx} <> fs, M6.and_right(M13.lxok(lx), M13.itsok(rest), M6.and_right(M13.allws(rws),
          Bool.and(M13.lxok(lx),
        M13.itsok(rest)), hi)),
        M6.and2(M13.allws(rws), Bool.and(M13.lxok(lx), M13.itsok(fs)), M6.and_left(M13.allws(rws),
            Bool.and(M13.lxok(lx), M13.itsok(rest)), hi),
        M6.and2(M13.lxok(lx), M13.itsok(fs), M6.and_left(M13.lxok(lx), M13.itsok(rest), M6.and_right(M13.allws(rws),
            Bool.and(M13.lxok(lx),
          M13.itsok(rest)), hi)), hf)))

# lexemes with no tokens are none
law its_nil:
  for its: List<&2, M6.It>
  for h: {M6.dens(M13.rtoks(its)) == [] : List<&2, Lex.Tok>}
  {its == [] : List<&2, M6.It>}

def its_nil(its, h):
  match its:
    case Nil{}:
      {==}
    case M6.It{+rws, +lx} <> +rest:
      Empty.absurd({M6.It{rws, lx} <> rest == [] : List<&2, M6.It>}, M1.true_false(Equal.cong(List<&2, Lex.Tok>, Bool,
        zz => M2.tnil(zz), [],
        M6.dens(M13.rtoks(M6.It{rws, lx} <> rest)), Equal.sym(List<&2, Lex.Tok>, M6.dens(M13.rtoks(M6.It{rws,
            lx} <> rest)), [], h))))

# whitespace read back as text is whitespace
law aw_text:
  for +ws: List<&2, Char>
  for +txt: String
  for +hw: {M13.allws(ws) == True{} : Bool}
  for ht: {D1.all_ws(txt) == True{} : Bool}
  {D1.all_ws(Lex.text.go(ws, txt)) == True{} : Bool}

def aw_text(ws, txt, hw, ht):
  match ws:
    case Nil{}:
      ht
    case +ch <> +tl:
      aw_text(tl, SCon{ch, txt}, M6.and_right(D1.is_ws(ch), M13.allws(tl), hw), M6.and2(D1.is_ws(ch), D1.all_ws(txt),
        M6.and_left(D1.is_ws(ch), M13.allws(tl), hw), ht))

# the last of four ors
law or4:
  for aa: Bool
  for bb: Bool
  for cc: Bool
  for dd: Bool
  for h: {dd == True{} : Bool}
  {Bool.or(aa, Bool.or(bb, Bool.or(cc, dd))) == True{} : Bool}

def or4(aa, bb, cc, _dd, h):
  match aa:
    case True{}:
      {==}
    case False{}:
      match bb:
        case True{}:
          {==}
        case False{}:
          match cc:
            case True{}:
              {==}
            case False{}:
              h

# a character list with nothing after it
law capp_nil:
  for +xs: List<&2, Char>
  {List.append(&2, Char, xs, []) == xs : List<&2, Char>}

def capp_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      Equal.cong(List<&2, Char>, List<&2, Char>, zz => hd <> zz, List.append(&2, Char, tl, []), tl, capp_nil(tl))

# a character list reversed twice
law crr:
  for +xs: List<&2, Char>
  for +acc: List<&2, Char>
  for +ys: List<&2, Char>
  {List.reverse.go(&2, Char, List.reverse.go(&2, Char, xs, acc), ys) == List.reverse.go(&2, Char, acc,
    List.append(&2, Char, xs, ys)) : List<&2, Char>}

def crr(xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      crr(tl, hd <> acc, ys)

# a string's characters make it again
law sfl:
  for +txt: String
  {String.from_list(String.to_list(txt)) == txt : String}

def sfl(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{+ch, +tl}:
      Equal.cong(String, String, zz => SCon{ch, zz}, String.from_list(String.to_list(tl)), tl, sfl(tl))

# a string's characters, reversed twice
law str_rr:
  for +txt: String
  {String.from_list(List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(txt), []), [])) == txt : String}

def str_rr(txt):
  Equal.trans(String, String.from_list(List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(txt), []),
    [])),
    String.from_list(String.to_list(txt)), txt, Equal.cong(List<&2, Char>, String, zz => String.from_list(zz),
    List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(txt), []), []), String.to_list(txt),
      Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(txt), []), []),
      List.append(&2, Char, String.to_list(txt), []),
    String.to_list(txt), crr(String.to_list(txt), [], []), capp_nil(String.to_list(txt)))), sfl(txt))

# two strings whose characters reverse alike are the same
law rc_inj:
  for +aa: String
  for +bb: String
  for h: {List.reverse.go(&2, Char, String.to_list(aa), []) == List.reverse.go(&2, Char, String.to_list(bb),
    []) : List<&2, Char>}
  {aa == bb : String}

def rc_inj(aa, bb, h):
  Equal.trans(String, aa, String.from_list(List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(aa), []),
    [])), bb, Equal.sym(String, String.from_list(List.reverse.go(&2, Char, List.reverse.go(&2, Char,
    String.to_list(aa), []), [])), aa, str_rr(aa)), Equal.trans(String, String.from_list(List.reverse.go(&2, Char,
    List.reverse.go(&2, Char, String.to_list(aa), []), [])), String.from_list(List.reverse.go(&2, Char,
    List.reverse.go(&2, Char, String.to_list(bb), []), [])), bb, Equal.cong(List<&2, Char>, String,
    zz => String.from_list(List.reverse.go(&2, Char, zz, [])), List.reverse.go(&2, Char, String.to_list(aa), []),
    List.reverse.go(&2, Char, String.to_list(bb), []), h), str_rr(bb)))

# the next lexeme is Lex.TOpenArr{}'s
law take_oa:
  for fits: List<&2, M6.It>
  for +rr: List<&2, Lex.Tok>
  for +acc: List<&2, Char>
  for +ht: {M6.dens(M13.rtoks(fits)) == Lex.TOpenArr{} <> rr : List<&2, Lex.Tok>}
  for +ho: {M13.itsok(fits) == True{} : Bool}
  (&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(tr,
    '[' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))))

def take_oa(fits, rr, acc, ht, ho):
  match fits:
    case Nil{}:
      Empty.absurd(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr([], acc) == M6.fr(tr,
        '[' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), M1.true_false(Equal.cong(List<&2, Lex.Tok>, Bool,
        zz => M2.tnil(zz), [], Lex.TOpenArr{} <> rr, ht)))
    case M6.It{+w, M6.LP{+ch}} <> +rest:
      (w, (rest, (Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M2.ttail(zz),
          M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)),
        Lex.TOpenArr{} <> rr, ht), (M6.and_right(M13.allws(w), Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho),
            (M6.and_left(M13.allws(w),
        Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho), Equal.cong(Char, List<&2, Char>, zz => M6.fr(rest,
            zz <> List.append(&2,
        Char, w, acc)), ch, '[', lp_inv(ch, Lex.TOpenArr{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz),
        M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)), Lex.TOpenArr{} <> rr, ht))))))))
    case M6.It{+w, M6.LW{+ww}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LW{ww}} <> rest,
        acc) == M6.fr(tr, '[' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 1), Lex.TWord{ww}, Lex.TOpenArr{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok,
        zz => M2.thead(zz), Lex.TWord{ww} <> M6.dens(M13.rtoks(rest)), Lex.TOpenArr{} <> rr, ht)))
    case M6.It{+w, M6.LS{+ps}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LS{ps}} <> rest,
        acc) == M6.fr(tr, '[' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 1), Lex.TStr{D2.spelled(ps)}, Lex.TOpenArr{}, Equal.cong(List<&2, Lex.Tok>,
        Lex.Tok, zz => M2.thead(zz), Lex.TStr{D2.spelled(ps)} <> M6.dens(M13.rtoks(rest)), Lex.TOpenArr{} <> rr, ht)))

# the next lexeme is Lex.TCloseArr{}'s
law take_ca:
  for fits: List<&2, M6.It>
  for +rr: List<&2, Lex.Tok>
  for +acc: List<&2, Char>
  for +ht: {M6.dens(M13.rtoks(fits)) == Lex.TCloseArr{} <> rr : List<&2, Lex.Tok>}
  for +ho: {M13.itsok(fits) == True{} : Bool}
  (&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(tr,
    ']' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))))

def take_ca(fits, rr, acc, ht, ho):
  match fits:
    case Nil{}:
      Empty.absurd(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr([], acc) == M6.fr(tr,
        ']' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), M1.true_false(Equal.cong(List<&2, Lex.Tok>, Bool,
        zz => M2.tnil(zz), [], Lex.TCloseArr{} <> rr, ht)))
    case M6.It{+w, M6.LP{+ch}} <> +rest:
      (w, (rest, (Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M2.ttail(zz),
          M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)),
        Lex.TCloseArr{} <> rr, ht), (M6.and_right(M13.allws(w), Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho),
            (M6.and_left(M13.allws(w),
        Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho), Equal.cong(Char, List<&2, Char>, zz => M6.fr(rest,
            zz <> List.append(&2,
        Char, w, acc)), ch, ']', lp_inv(ch, Lex.TCloseArr{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz),
        M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)), Lex.TCloseArr{} <> rr, ht))))))))
    case M6.It{+w, M6.LW{+ww}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LW{ww}} <> rest,
        acc) == M6.fr(tr, ']' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 2), Lex.TWord{ww}, Lex.TCloseArr{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok,
        zz => M2.thead(zz), Lex.TWord{ww} <> M6.dens(M13.rtoks(rest)), Lex.TCloseArr{} <> rr, ht)))
    case M6.It{+w, M6.LS{+ps}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LS{ps}} <> rest,
        acc) == M6.fr(tr, ']' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 2), Lex.TStr{D2.spelled(ps)}, Lex.TCloseArr{}, Equal.cong(List<&2, Lex.Tok>,
        Lex.Tok, zz => M2.thead(zz), Lex.TStr{D2.spelled(ps)} <> M6.dens(M13.rtoks(rest)), Lex.TCloseArr{} <> rr, ht)))

# the next lexeme is Lex.TOpenObj{}'s
law take_oo:
  for fits: List<&2, M6.It>
  for +rr: List<&2, Lex.Tok>
  for +acc: List<&2, Char>
  for +ht: {M6.dens(M13.rtoks(fits)) == Lex.TOpenObj{} <> rr : List<&2, Lex.Tok>}
  for +ho: {M13.itsok(fits) == True{} : Bool}
  (&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(tr,
    '{' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))))

def take_oo(fits, rr, acc, ht, ho):
  match fits:
    case Nil{}:
      Empty.absurd(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr([], acc) == M6.fr(tr,
        '{' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), M1.true_false(Equal.cong(List<&2, Lex.Tok>, Bool,
        zz => M2.tnil(zz), [], Lex.TOpenObj{} <> rr, ht)))
    case M6.It{+w, M6.LP{+ch}} <> +rest:
      (w, (rest, (Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M2.ttail(zz),
          M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)),
        Lex.TOpenObj{} <> rr, ht), (M6.and_right(M13.allws(w), Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho),
            (M6.and_left(M13.allws(w),
        Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho), Equal.cong(Char, List<&2, Char>, zz => M6.fr(rest,
            zz <> List.append(&2,
        Char, w, acc)), ch, '{', lp_inv(ch, Lex.TOpenObj{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz),
        M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)), Lex.TOpenObj{} <> rr, ht))))))))
    case M6.It{+w, M6.LW{+ww}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LW{ww}} <> rest,
        acc) == M6.fr(tr, '{' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 3), Lex.TWord{ww}, Lex.TOpenObj{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok,
        zz => M2.thead(zz), Lex.TWord{ww} <> M6.dens(M13.rtoks(rest)), Lex.TOpenObj{} <> rr, ht)))
    case M6.It{+w, M6.LS{+ps}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LS{ps}} <> rest,
        acc) == M6.fr(tr, '{' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 3), Lex.TStr{D2.spelled(ps)}, Lex.TOpenObj{}, Equal.cong(List<&2, Lex.Tok>,
        Lex.Tok, zz => M2.thead(zz), Lex.TStr{D2.spelled(ps)} <> M6.dens(M13.rtoks(rest)), Lex.TOpenObj{} <> rr, ht)))

# the next lexeme is Lex.TCloseObj{}'s
law take_co:
  for fits: List<&2, M6.It>
  for +rr: List<&2, Lex.Tok>
  for +acc: List<&2, Char>
  for +ht: {M6.dens(M13.rtoks(fits)) == Lex.TCloseObj{} <> rr : List<&2, Lex.Tok>}
  for +ho: {M13.itsok(fits) == True{} : Bool}
  (&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(tr,
    '}' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))))

def take_co(fits, rr, acc, ht, ho):
  match fits:
    case Nil{}:
      Empty.absurd(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr([], acc) == M6.fr(tr,
        '}' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), M1.true_false(Equal.cong(List<&2, Lex.Tok>, Bool,
        zz => M2.tnil(zz), [], Lex.TCloseObj{} <> rr, ht)))
    case M6.It{+w, M6.LP{+ch}} <> +rest:
      (w, (rest, (Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M2.ttail(zz),
          M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)),
        Lex.TCloseObj{} <> rr, ht), (M6.and_right(M13.allws(w), Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho),
            (M6.and_left(M13.allws(w),
        Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho), Equal.cong(Char, List<&2, Char>, zz => M6.fr(rest,
            zz <> List.append(&2,
        Char, w, acc)), ch, '}', lp_inv(ch, Lex.TCloseObj{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz),
        M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)), Lex.TCloseObj{} <> rr, ht))))))))
    case M6.It{+w, M6.LW{+ww}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LW{ww}} <> rest,
        acc) == M6.fr(tr, '}' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 4), Lex.TWord{ww}, Lex.TCloseObj{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok,
        zz => M2.thead(zz), Lex.TWord{ww} <> M6.dens(M13.rtoks(rest)), Lex.TCloseObj{} <> rr, ht)))
    case M6.It{+w, M6.LS{+ps}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LS{ps}} <> rest,
        acc) == M6.fr(tr, '}' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 4), Lex.TStr{D2.spelled(ps)}, Lex.TCloseObj{}, Equal.cong(List<&2, Lex.Tok>,
        Lex.Tok, zz => M2.thead(zz), Lex.TStr{D2.spelled(ps)} <> M6.dens(M13.rtoks(rest)), Lex.TCloseObj{} <> rr, ht)))

# the next lexeme is Lex.TColon{}'s
law take_col:
  for fits: List<&2, M6.It>
  for +rr: List<&2, Lex.Tok>
  for +acc: List<&2, Char>
  for +ht: {M6.dens(M13.rtoks(fits)) == Lex.TColon{} <> rr : List<&2, Lex.Tok>}
  for +ho: {M13.itsok(fits) == True{} : Bool}
  (&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(tr,
    ':' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))))

def take_col(fits, rr, acc, ht, ho):
  match fits:
    case Nil{}:
      Empty.absurd(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr([], acc) == M6.fr(tr,
        ':' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), M1.true_false(Equal.cong(List<&2, Lex.Tok>, Bool,
        zz => M2.tnil(zz), [], Lex.TColon{} <> rr, ht)))
    case M6.It{+w, M6.LP{+ch}} <> +rest:
      (w, (rest, (Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M2.ttail(zz),
          M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)),
        Lex.TColon{} <> rr, ht), (M6.and_right(M13.allws(w), Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho),
            (M6.and_left(M13.allws(w),
        Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho), Equal.cong(Char, List<&2, Char>, zz => M6.fr(rest,
            zz <> List.append(&2,
        Char, w, acc)), ch, ':', lp_inv(ch, Lex.TColon{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz),
        M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)), Lex.TColon{} <> rr, ht))))))))
    case M6.It{+w, M6.LW{+ww}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LW{ww}} <> rest,
        acc) == M6.fr(tr, ':' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 5), Lex.TWord{ww}, Lex.TColon{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok,
        zz => M2.thead(zz), Lex.TWord{ww} <> M6.dens(M13.rtoks(rest)), Lex.TColon{} <> rr, ht)))
    case M6.It{+w, M6.LS{+ps}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LS{ps}} <> rest,
        acc) == M6.fr(tr, ':' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 5), Lex.TStr{D2.spelled(ps)}, Lex.TColon{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok,
        zz => M2.thead(zz), Lex.TStr{D2.spelled(ps)} <> M6.dens(M13.rtoks(rest)), Lex.TColon{} <> rr, ht)))

# the next lexeme is Lex.TComma{}'s
law take_com:
  for fits: List<&2, M6.It>
  for +rr: List<&2, Lex.Tok>
  for +acc: List<&2, Char>
  for +ht: {M6.dens(M13.rtoks(fits)) == Lex.TComma{} <> rr : List<&2, Lex.Tok>}
  for +ho: {M13.itsok(fits) == True{} : Bool}
  (&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(tr,
    ',' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))))

def take_com(fits, rr, acc, ht, ho):
  match fits:
    case Nil{}:
      Empty.absurd(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr([], acc) == M6.fr(tr,
        ',' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), M1.true_false(Equal.cong(List<&2, Lex.Tok>, Bool,
        zz => M2.tnil(zz), [], Lex.TComma{} <> rr, ht)))
    case M6.It{+w, M6.LP{+ch}} <> +rest:
      (w, (rest, (Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M2.ttail(zz),
          M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)),
        Lex.TComma{} <> rr, ht), (M6.and_right(M13.allws(w), Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho),
            (M6.and_left(M13.allws(w),
        Bool.and(M13.lxok(M6.LP{ch}), M13.itsok(rest)), ho), Equal.cong(Char, List<&2, Char>, zz => M6.fr(rest,
            zz <> List.append(&2,
        Char, w, acc)), ch, ',', lp_inv(ch, Lex.TComma{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz),
        M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)), Lex.TComma{} <> rr, ht))))))))
    case M6.It{+w, M6.LW{+ww}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LW{ww}} <> rest,
        acc) == M6.fr(tr, ',' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 6), Lex.TWord{ww}, Lex.TComma{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok,
        zz => M2.thead(zz), Lex.TWord{ww} <> M6.dens(M13.rtoks(rest)), Lex.TComma{} <> rr, ht)))
    case M6.It{+w, M6.LS{+ps}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LS{ps}} <> rest,
        acc) == M6.fr(tr, ',' <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))), Equal.cong(Lex.Tok, Bool,
        zz => U32.is_eq(ttag(zz), 6), Lex.TStr{D2.spelled(ps)}, Lex.TComma{}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok,
        zz => M2.thead(zz), Lex.TStr{D2.spelled(ps)} <> M6.dens(M13.rtoks(rest)), Lex.TComma{} <> rr, ht)))

# the next lexeme is Lex.TWord{xx}'s
law take_w:
  for fits: List<&2, M6.It>
  for +xx: String
  for +rr: List<&2, Lex.Tok>
  for +acc: List<&2, Char>
  for +ht: {M6.dens(M13.rtoks(fits)) == Lex.TWord{xx} <> rr : List<&2, Lex.Tok>}
  for +ho: {M13.itsok(fits) == True{} : Bool}
  (&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(tr,
    List.reverse.go(&2, Char, String.to_list(xx), List.append(&2, Char, tw, acc))) : List<&2, Char>}))))

def take_w(fits, xx, rr, acc, ht, ho):
  match fits:
    case Nil{}:
      Empty.absurd(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr([], acc) == M6.fr(tr,
        List.reverse.go(&2, Char, String.to_list(xx), List.append(&2, Char, tw, acc))) : List<&2, Char>}))),
        M1.true_false(Equal.cong(List<&2, Lex.Tok>, Bool, zz => M2.tnil(zz), [], Lex.TWord{xx} <> rr, ht)))
    case M6.It{+w, M6.LP{+ch}} <> +rest:
      Empty.absurd(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LP{ch}} <> rest,
        acc) == M6.fr(tr, List.reverse.go(&2, Char, String.to_list(xx), List.append(&2, Char, tw, acc))) : List<&2,
        Char>}))), lp_inv(ch, Lex.TWord{xx}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz),
        M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)), Lex.TWord{xx} <> rr, ht)))
    case M6.It{+w, M6.LW{+ww}} <> +rest:
      (w, (rest, (Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M2.ttail(zz),
          Lex.TWord{ww} <> M6.dens(M13.rtoks(rest)),
        Lex.TWord{xx} <> rr, ht), (M6.and_right(M13.allws(w), Bool.and(M13.lxok(M6.LW{ww}), M13.itsok(rest)), ho),
            (M6.and_left(M13.allws(w),
        Bool.and(M13.lxok(M6.LW{ww}), M13.itsok(rest)), ho), Equal.cong(String, List<&2, Char>, zz => M6.fr(rest,
            List.reverse.go(&2,
        Char, String.to_list(zz), List.append(&2, Char, w, acc))), ww, xx, Equal.cong(Lex.Tok, String, zz => twd(zz),
        Lex.TWord{ww}, Lex.TWord{xx}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz),
        Lex.TWord{ww} <> M6.dens(M13.rtoks(rest)), Lex.TWord{xx} <> rr, ht))))))))
    case M6.It{+w, M6.LS{+ps}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(M6.It{w,
            M6.LS{ps}} <> rest,
        acc) == M6.fr(tr, List.reverse.go(&2, Char, String.to_list(xx), List.append(&2, Char, tw, acc))) : List<&2,
        Char>}))), Equal.cong(Lex.Tok, Bool, zz => U32.is_eq(ttag(zz), 8), Lex.TStr{D2.spelled(ps)}, Lex.TWord{xx},
        Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz), Lex.TStr{D2.spelled(ps)} <> M6.dens(M13.rtoks(rest)),
        Lex.TWord{xx} <> rr, ht)))

# the next lexeme is Lex.TStr{xx}'s
law take_s:
  for fits: List<&2, M6.It>
  for +xx: String
  for +rr: List<&2, Lex.Tok>
  for +acc: List<&2, Char>
  for +ht: {M6.dens(M13.rtoks(fits)) == Lex.TStr{xx} <> rr : List<&2, Lex.Tok>}
  for +ho: {M13.itsok(fits) == True{} : Bool}
  (&tw: List<&2, Char> -> &tp: List<&2, D2.Piece> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & ({D2.spell_ok(tp) ==
    True{} : Bool} & ({D2.spelled(tp) == xx : String} & {M6.fr(fits, acc) == M6.fr(tr, '"' <> List.reverse.go(&2, Char,
    String.to_list(D2.spell(tp)), '"' <> List.append(&2, Char, tw, acc))) : List<&2, Char>}))))))

def take_s(fits, xx, rr, acc, ht, ho):
  match fits:
    case Nil{}:
      Empty.absurd(&tw: List<&2, Char> -> &tp: List<&2, D2.Piece> -> &tr: List<&2,
        M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & ({D2.spell_ok(tp) ==
        True{} : Bool} & ({D2.spelled(tp) == xx : String} & {M6.fr([], acc) == M6.fr(tr, '"' <> List.reverse.go(&2,
            Char,
        String.to_list(D2.spell(tp)), '"' <> List.append(&2, Char, tw, acc))) : List<&2, Char>}))))),
        M1.true_false(Equal.cong(List<&2, Lex.Tok>, Bool, zz => M2.tnil(zz), [], Lex.TStr{xx} <> rr, ht)))
    case M6.It{+w, M6.LP{+ch}} <> +rest:
      Empty.absurd(&tw: List<&2, Char> -> &tp: List<&2, D2.Piece> -> &tr: List<&2,
        M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & ({D2.spell_ok(tp) ==
        True{} : Bool} & ({D2.spelled(tp) == xx : String} & {M6.fr(M6.It{w, M6.LP{ch}} <> rest, acc) == M6.fr(tr,
        '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(tp)), '"' <> List.append(&2, Char, tw,
        acc))) : List<&2, Char>}))))), lp_inv(ch, Lex.TStr{xx}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok,
            zz => M2.thead(zz),
        M6.den(M13.ptok(ch)) <> M6.dens(M13.rtoks(rest)), Lex.TStr{xx} <> rr, ht)))
    case M6.It{+w, M6.LW{+ww}} <> +rest:
      M6.no(&tw: List<&2, Char> -> &tp: List<&2, D2.Piece> -> &tr: List<&2,
          M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & ({D2.spell_ok(tp) ==
        True{} : Bool} & ({D2.spelled(tp) == xx : String} & {M6.fr(M6.It{w, M6.LW{ww}} <> rest, acc) == M6.fr(tr,
        '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(tp)), '"' <> List.append(&2, Char, tw,
        acc))) : List<&2, Char>}))))), Equal.cong(Lex.Tok, Bool, zz => U32.is_eq(ttag(zz), 7), Lex.TWord{ww},
        Lex.TStr{xx}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz),
            Lex.TWord{ww} <> M6.dens(M13.rtoks(rest)),
        Lex.TStr{xx} <> rr, ht)))
    case M6.It{+w, M6.LS{+ps}} <> +rest:
      (w, (ps, (rest, (Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M2.ttail(zz),
        Lex.TStr{D2.spelled(ps)} <> M6.dens(M13.rtoks(rest)), Lex.TStr{xx} <> rr, ht), (M6.and_right(D2.spell_ok(ps),
        M13.itsok(rest), M6.and_right(M13.allws(w), Bool.and(D2.spell_ok(ps), M13.itsok(rest)), ho)),
            (M6.and_left(M13.allws(w),
        Bool.and(M13.lxok(M6.LS{ps}), M13.itsok(rest)), ho), (M6.and_left(D2.spell_ok(ps), M13.itsok(rest),
            M6.and_right(M13.allws(w),
        Bool.and(D2.spell_ok(ps), M13.itsok(rest)), ho)), (Equal.cong(Lex.Tok, String, zz => tsd(zz),
        Lex.TStr{D2.spelled(ps)}, Lex.TStr{xx}, Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz),
        Lex.TStr{D2.spelled(ps)} <> M6.dens(M13.rtoks(rest)), Lex.TStr{xx} <> rr, ht)), {==}))))))))

# the tokens of an array's cells after an element
def ctk(cells: V.Json) -> List<&2, Lex.Tok>:
  match cells:
    case V.JNil{}:
      []
    case other:
      Lex.TComma{} <> M13.tj_r(other, V.WArr{})

# the tokens of an object's cells after a member
def otk(cells: V.Json) -> List<&2, Lex.Tok>:
  match cells:
    case V.JNil{}:
      []
    case other:
      Lex.TComma{} <> M13.tj_r(other, V.WObj{})

# the tokens bld reads: a value's, or cells' and their closing bracket, then rr
def btk(val: V.Json, sh: V.Shape, rr: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match sh:
    case V.WVal{}:
      List.append(&2, Lex.Tok, M13.tj_r(val, V.WVal{}), rr)
    case V.WArr{}:
      List.append(&2, Lex.Tok, ctk(val), Lex.TCloseArr{} <> rr)
    case V.WObj{}:
      List.append(&2, Lex.Tok, otk(val), Lex.TCloseObj{} <> rr)

# what bld gives: whitespace, a derivation and the lexemes left, the lexemes
# read spelling the whitespace and the derivation (and a closing bracket)
def bldg(sh: V.Shape, +fits: List<&2, M6.It>, +rr: List<&2, Lex.Tok>, +acc: List<&2, Char>) -> Type:
  match sh:
    case V.WVal{}:
      &bw: List<&2, Char> -> &bg: D2.Gv -> &br: List<&2, M6.It> -> ({M6.dens(M13.rtoks(br)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(br) == True{} : Bool} &
        ({M13.allws(bw) == True{} : Bool} & ({D2.g.ok(bg, D2.GKVal{}) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(br,
        List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2, Char, bw, acc))) : List<&2,
          Char>}))))
    case V.WArr{}:
      &bw: List<&2, Char> -> &bg: D2.Gv -> &br: List<&2, M6.It> -> ({M6.dens(M13.rtoks(br)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(br) == True{} : Bool} &
        ({M13.allws(bw) == True{} : Bool} & ({D2.g.ok(bg, D2.GKArr{}) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(br,
        ']' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2, Char, bw, acc))) : List<&2,
          Char>}))))
    case V.WObj{}:
      &bw: List<&2, Char> -> &bg: D2.Gv -> &br: List<&2, M6.It> -> ({M6.dens(M13.rtoks(br)) == rr : List<&2,
        Lex.Tok>} & ({M13.itsok(br) == True{} : Bool} &
        ({M13.allws(bw) == True{} : Bool} & ({D2.g.ok(bg, D2.GKObj{}) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(br,
        '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2, Char, bw, acc))) : List<&2,
          Char>}))))

# a cell's tokens, then kt
law ctoks:
  for +vv: V.Json
  for cc: V.Json
  for +kt: List<&2, Lex.Tok>
  {List.append(&2, Lex.Tok, M13.tj_r(V.JCons{vv, cc}, V.WArr{}), kt) == List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
    List.append(&2, Lex.Tok, ctk(cc), kt)) : List<&2, Lex.Tok>}

def ctoks(vv, cc, kt):
  match cc:
    case V.JNull{}:
      M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JNull{}, V.WArr{}), kt)
    case V.JBool{+x1}:
      M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JBool{x1}, V.WArr{}), kt)
    case V.JNum{+x1}:
      M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JNum{x1}, V.WArr{}), kt)
    case V.JStr{+x1}:
      M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JStr{x1}, V.WArr{}), kt)
    case V.JArr{+x1}:
      M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JArr{x1}, V.WArr{}), kt)
    case V.JObj{+x1}:
      M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JObj{x1}, V.WArr{}), kt)
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JCons{x1, x2}, V.WArr{}), kt)
    case V.JPair{+x1, +x2, +x3}:
      M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JPair{x1, x2, x3}, V.WArr{}), kt)
    case V.JSpan{+x1, +x2}:
      M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JSpan{x1, x2}, V.WArr{}), kt)
    case V.JBind{+x1, +x2, +x3, +x4}:
      M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JBind{x1, x2, x3, x4}, V.WArr{}), kt)

# a cell's tokens, then kt
law ptoks:
  for +kk: String
  for +vv: V.Json
  for cc: V.Json
  for +kt: List<&2, Lex.Tok>
  {List.append(&2, Lex.Tok, M13.tj_r(V.JPair{kk, vv, cc}, V.WObj{}),
      kt) == Lex.TStr{kk} <> Lex.TColon{} <> List.append(&2,
    Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok, otk(cc), kt)) : List<&2, Lex.Tok>}

def ptoks(kk, vv, cc, kt):
  match cc:
    case V.JNull{}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{kk} <> Lex.TColon{} <> zz, List.append(&2,
        Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JNull{}, V.WObj{})), kt),
        List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JNull{},
        V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JNull{}, V.WObj{}), kt))
    case V.JBool{+x1}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{kk} <> Lex.TColon{} <> zz, List.append(&2,
        Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JBool{x1}, V.WObj{})), kt),
        List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JBool{x1},
        V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JBool{x1}, V.WObj{}), kt))
    case V.JNum{+x1}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{kk} <> Lex.TColon{} <> zz, List.append(&2,
        Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JNum{x1}, V.WObj{})), kt),
        List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JNum{x1},
        V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JNum{x1}, V.WObj{}), kt))
    case V.JStr{+x1}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{kk} <> Lex.TColon{} <> zz, List.append(&2,
        Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JStr{x1}, V.WObj{})), kt),
        List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JStr{x1},
        V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JStr{x1}, V.WObj{}), kt))
    case V.JArr{+x1}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{kk} <> Lex.TColon{} <> zz, List.append(&2,
        Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JArr{x1}, V.WObj{})), kt),
        List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JArr{x1},
        V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JArr{x1}, V.WObj{}), kt))
    case V.JObj{+x1}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{kk} <> Lex.TColon{} <> zz, List.append(&2,
        Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JObj{x1}, V.WObj{})), kt),
        List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JObj{x1},
        V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JObj{x1}, V.WObj{}), kt))
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{kk} <> Lex.TColon{} <> zz, List.append(&2,
        Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JCons{x1, x2}, V.WObj{})),
            kt),
        List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JCons{x1,
            x2},
        V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JCons{x1, x2}, V.WObj{}), kt))
    case V.JPair{+x1, +x2, +x3}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{kk} <> Lex.TColon{} <> zz, List.append(&2,
        Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JPair{x1, x2, x3},
            V.WObj{})),
        kt), List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok,
            Lex.TComma{} <> M13.tj_r(V.JPair{x1, x2,
        x3}, V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JPair{x1, x2, x3},
            V.WObj{}), kt))
    case V.JSpan{+x1, +x2}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{kk} <> Lex.TColon{} <> zz, List.append(&2,
        Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JSpan{x1, x2}, V.WObj{})),
            kt),
        List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JSpan{x1,
            x2},
        V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JSpan{x1, x2}, V.WObj{}), kt))
    case V.JBind{+x1, +x2, +x3, +x4}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{kk} <> Lex.TColon{} <> zz, List.append(&2,
        Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JBind{x1, x2, x3, x4},
            V.WObj{})),
        kt), List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok,
            Lex.TComma{} <> M13.tj_r(V.JBind{x1, x2,
        x3, x4}, V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JBind{x1, x2, x3,
            x4},
        V.WObj{}), kt))

# a cell's tokens, then kt
law btoks:
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for cc: V.Json
  for +kt: List<&2, Lex.Tok>
  {List.append(&2, Lex.Tok, M13.tj_r(V.JBind{src, nn, vv, cc}, V.WObj{}), kt) == Lex.TStr{V.span.str(src, nn,
    U32.is_zero(nn))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}), List.append(&2, Lex.Tok,
        otk(cc),
    kt)) : List<&2, Lex.Tok>}

def btoks(src, nn, vv, cc, kt):
  match cc:
    case V.JNull{}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> zz, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JNull{}, V.WObj{})), kt), List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
            List.append(&2,
        Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JNull{}, V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JNull{}, V.WObj{}), kt))
    case V.JBool{+x1}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> zz, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JBool{x1}, V.WObj{})), kt), List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
            List.append(&2,
        Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JBool{x1}, V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JBool{x1}, V.WObj{}), kt))
    case V.JNum{+x1}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> zz, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JNum{x1}, V.WObj{})), kt), List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
            List.append(&2,
        Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JNum{x1}, V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JNum{x1}, V.WObj{}), kt))
    case V.JStr{+x1}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> zz, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JStr{x1}, V.WObj{})), kt), List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
            List.append(&2,
        Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JStr{x1}, V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JStr{x1}, V.WObj{}), kt))
    case V.JArr{+x1}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> zz, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JArr{x1}, V.WObj{})), kt), List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
            List.append(&2,
        Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JArr{x1}, V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JArr{x1}, V.WObj{}), kt))
    case V.JObj{+x1}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> zz, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JObj{x1}, V.WObj{})), kt), List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
            List.append(&2,
        Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JObj{x1}, V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JObj{x1}, V.WObj{}), kt))
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> zz, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JCons{x1, x2}, V.WObj{})), kt), List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JCons{x1, x2}, V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JCons{x1, x2}, V.WObj{}), kt))
    case V.JPair{+x1, +x2, +x3}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> zz, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JPair{x1, x2, x3}, V.WObj{})), kt), List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JPair{x1, x2, x3}, V.WObj{}), kt)),
            M9.lapp_assoc(M13.tj_r(vv,
        V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JPair{x1, x2, x3}, V.WObj{}), kt))
    case V.JSpan{+x1, +x2}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> zz, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JSpan{x1, x2}, V.WObj{})), kt), List.append(&2, Lex.Tok, M13.tj_r(vv, V.WVal{}),
        List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JSpan{x1, x2}, V.WObj{}), kt)), M9.lapp_assoc(M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JSpan{x1, x2}, V.WObj{}), kt))
    case V.JBind{+x1, +x2, +x3, +x4}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{V.span.str(src, nn,
        U32.is_zero(nn))} <> Lex.TColon{} <> zz, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(vv,
            V.WVal{}),
        Lex.TComma{} <> M13.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{})), kt), List.append(&2, Lex.Tok, M13.tj_r(vv,
            V.WVal{}),
        List.append(&2, Lex.Tok, Lex.TComma{} <> M13.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{}), kt)),
            M9.lapp_assoc(M13.tj_r(vv,
        V.WVal{}), Lex.TComma{} <> M13.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{}), kt))

# a punctuation lexeme taken, passed on
law use_p:
  for -gl: Type
  for fits: List<&2, M6.It>
  for rr: List<&2, Lex.Tok>
  for acc: List<&2, Char>
  for pc: Char
  for r: (&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(tr,
    pc <> List.append(&2, Char, tw, acc)) : List<&2, Char>}))))
  for kk: @tw: List<&2, Char> -> @tr: List<&2, M6.It> -> {M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} -> {M13.itsok(tr) == True{} : Bool} -> {M13.allws(tw) == True{} : Bool} -> {M6.fr(fits, acc) == M6.fr(tr,
    pc <> List.append(&2, Char, tw, acc)) : List<&2, Char>} -> gl
  gl

def use_p(_gl, _fits, _rr, _acc, _pc, r, kk):
  (tw, (tr, (aa, (bb, (cc, dd))))) = r
  kk(tw, tr, aa, bb, cc, dd)

# a word lexeme taken, passed on
law use_w:
  for -gl: Type
  for fits: List<&2, M6.It>
  for xx: String
  for rr: List<&2, Lex.Tok>
  for acc: List<&2, Char>
  for r: (&tw: List<&2, Char> -> &tr: List<&2, M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} & ({M13.allws(tw) == True{} : Bool} & {M6.fr(fits, acc) == M6.fr(tr,
    List.reverse.go(&2, Char, String.to_list(xx), List.append(&2, Char, tw, acc))) : List<&2, Char>}))))
  for kk: @tw: List<&2, Char> -> @tr: List<&2, M6.It> -> {M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} -> {M13.itsok(tr) == True{} : Bool} -> {M13.allws(tw) == True{} : Bool} -> {M6.fr(fits, acc) == M6.fr(tr,
    List.reverse.go(&2, Char, String.to_list(xx), List.append(&2, Char, tw, acc))) : List<&2, Char>} -> gl
  gl

def use_w(_gl, _fits, _xx, _rr, _acc, r, kk):
  (tw, (tr, (aa, (bb, (cc, dd))))) = r
  kk(tw, tr, aa, bb, cc, dd)

# a string lexeme taken, passed on
law use_s:
  for -gl: Type
  for fits: List<&2, M6.It>
  for xx: String
  for rr: List<&2, Lex.Tok>
  for acc: List<&2, Char>
  for r: (&tw: List<&2, Char> -> &tp: List<&2, D2.Piece> -> &tr: List<&2,
      M6.It> -> ({M6.dens(M13.rtoks(tr)) == rr : List<&2,
    Lex.Tok>} & ({M13.itsok(tr) == True{} : Bool} &
    ({M13.allws(tw) == True{} : Bool} & ({D2.spell_ok(tp) == True{} : Bool} & ({D2.spelled(tp) == xx : String} &
    {M6.fr(fits, acc) == M6.fr(tr, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(tp)), '"' <> List.append(&2,
      Char, tw, acc))) : List<&2, Char>}))))))
  for kk: @tw: List<&2, Char> -> @tp: List<&2, D2.Piece> -> @tr: List<&2, M6.It> -> {M6.dens(M13.rtoks(tr)) == rr : List<&2,  # noqa: S002
    Lex.Tok>} -> {M13.itsok(tr) == True{} : Bool} ->
    {M13.allws(tw) == True{} : Bool} -> {D2.spell_ok(tp) == True{} : Bool} -> {D2.spelled(tp) == xx : String} ->
    {M6.fr(fits, acc) == M6.fr(tr, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(tp)), '"' <> List.append(&2,
      Char, tw, acc))) : List<&2, Char>} -> gl
  gl

def use_s(_gl, _fits, _xx, _rr, _acc, r, kk):
  (tw, (tp, (tr, (aa, (bb, (cc, (dd, (ee, ff)))))))) = r
  kk(tw, tp, tr, aa, bb, cc, dd, ee, ff)

# a derivation built, passed on
law use_bv:
  for -gl: Type
  for fits: List<&2, M6.It>
  for rr: List<&2, Lex.Tok>
  for acc: List<&2, Char>
  for r: bldg(V.WVal{}, fits, rr, acc)
  for kk: @bw: List<&2, Char> -> @bg: D2.Gv -> @br: List<&2, M6.It> -> {M6.dens(M13.rtoks(br)) == rr : List<&2,
    Lex.Tok>} -> {M13.itsok(br) == True{} : Bool} ->
    {M13.allws(bw) == True{} : Bool} -> {D2.g.ok(bg, D2.GKVal{}) == True{} : Bool} -> {M6.fr(fits, acc) == M6.fr(br,
    List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2, Char, bw, acc))) : List<&2, Char>} -> gl
  gl

def use_bv(_gl, _fits, _rr, _acc, r, kk):
  (bw, (bg, (br, (aa, (bb, (cc, (dd, ee))))))) = r
  kk(bw, bg, br, aa, bb, cc, dd, ee)

# a derivation built, passed on
law use_ba:
  for -gl: Type
  for fits: List<&2, M6.It>
  for rr: List<&2, Lex.Tok>
  for acc: List<&2, Char>
  for r: bldg(V.WArr{}, fits, rr, acc)
  for kk: @bw: List<&2, Char> -> @bg: D2.Gv -> @br: List<&2, M6.It> -> {M6.dens(M13.rtoks(br)) == rr : List<&2,
    Lex.Tok>} -> {M13.itsok(br) == True{} : Bool} ->
    {M13.allws(bw) == True{} : Bool} -> {D2.g.ok(bg, D2.GKArr{}) == True{} : Bool} -> {M6.fr(fits, acc) == M6.fr(br,
    ']' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2, Char, bw, acc))) : List<&2,
      Char>} -> gl
  gl

def use_ba(_gl, _fits, _rr, _acc, r, kk):
  (bw, (bg, (br, (aa, (bb, (cc, (dd, ee))))))) = r
  kk(bw, bg, br, aa, bb, cc, dd, ee)

# a derivation built, passed on
law use_bo:
  for -gl: Type
  for fits: List<&2, M6.It>
  for rr: List<&2, Lex.Tok>
  for acc: List<&2, Char>
  for r: bldg(V.WObj{}, fits, rr, acc)
  for kk: @bw: List<&2, Char> -> @bg: D2.Gv -> @br: List<&2, M6.It> -> {M6.dens(M13.rtoks(br)) == rr : List<&2,
    Lex.Tok>} -> {M13.itsok(br) == True{} : Bool} ->
    {M13.allws(bw) == True{} : Bool} -> {D2.g.ok(bg, D2.GKObj{}) == True{} : Bool} -> {M6.fr(fits, acc) == M6.fr(br,
    '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2, Char, bw, acc))) : List<&2,
      Char>} -> gl
  gl

def use_bo(_gl, _fits, _rr, _acc, r, kk):
  (bw, (bg, (br, (aa, (bb, (cc, (dd, ee))))))) = r
  kk(bw, bg, br, aa, bb, cc, dd, ee)

# a derivation read off lexemes whose tokens are a well-formed value's, or
# an array's or object's cells' and closing bracket
law bld:
  for val: V.Json
  for sh: V.Shape
  for +fits: List<&2, M6.It>
  for +rr: List<&2, Lex.Tok>
  for +acc: List<&2, Char>
  for +hw: {V.wf.go(val, sh) == True{} : Bool}
  for +ht: {M6.dens(M13.rtoks(fits)) == btk(val, sh, rr) : List<&2, Lex.Tok>}
  for +ho: {M13.itsok(fits) == True{} : Bool}
  bldg(sh, fits, rr, acc)

def bld(val, sh, fits, rr, acc, hw, ht, ho):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          use_w(bldg(V.WVal{}, fits, rr, acc), fits, "null", rr, acc, take_w(fits, "null", rr, acc, ht, ho),
            +w => +f1 => t1 => o1 => a1 => e1 => (w, (D2.GWord{"null"}, (f1, (t1, (o1, (a1, ({==}, e1))))))))
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JBool{True{}}:
      match sh:
        case V.WVal{}:
          use_w(bldg(V.WVal{}, fits, rr, acc), fits, "true", rr, acc, take_w(fits, "true", rr, acc, ht, ho),
            +w => +f1 => t1 => o1 => a1 => e1 => (w, (D2.GWord{"true"}, (f1, (t1, (o1, (a1, ({==}, e1))))))))
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JBool{False{}}:
      match sh:
        case V.WVal{}:
          use_w(bldg(V.WVal{}, fits, rr, acc), fits, "false", rr, acc, take_w(fits, "false", rr, acc, ht, ho),
            +w => +f1 => t1 => o1 => a1 => e1 => (w, (D2.GWord{"false"}, (f1, (t1, (o1, (a1, ({==}, e1))))))))
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JNum{+x1}:
      match sh:
        case V.WVal{}:
          use_w(bldg(V.WVal{}, fits, rr, acc), fits, x1, rr, acc, take_w(fits, x1, rr, acc, ht, ho),
            +w => +f1 => t1 => o1 => a1 => e1 => (w, (D2.GWord{x1}, (f1, (t1, (o1, (a1, (or4(String.eq(x1, "null"),
            String.eq(x1, "true"), String.eq(x1, "false"), D1.number(String.to_list(x1)), Equal.trans(Bool,
            D1.number(String.to_list(x1)), V.num.ok(x1), True{}, Equal.sym(Bool, V.num.ok(x1),
            D1.number(String.to_list(x1)), L2.num_grammar(x1)), hw)), e1))))))))
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JStr{+x1}:
      match sh:
        case V.WVal{}:
          use_s(bldg(V.WVal{}, fits, rr, acc), fits, x1, rr, acc, take_s(fits, x1, rr, acc, ht, ho),
            +w => +ps => +f1 => t1 => o1 => a1 => okp => _esp => e1 => (w, (D2.GStr{ps}, (f1, (t1, (o1, (a1, (okp,
            Equal.trans(List<&2, Char>, M6.fr(fits, acc), M6.fr(f1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w, acc))), M6.fr(f1, List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\""), List.append(&2, Char, w, acc))), e1, Equal.cong(List<&2,
            Char>, List<&2, Char>, zz => M6.fr(f1, zz), '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w, acc)), List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\""), List.append(&2, Char, w, acc)), Equal.sym(List<&2, Char>,
            List.reverse.go(&2, Char, String.to_list("\"" ++ D2.spell(ps) ++ "\""), List.append(&2, Char, w, acc)),
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w, acc)),
            Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list("\"" ++ D2.spell(ps) ++ "\""),
            List.append(&2, Char, w, acc)), List.reverse.go(&2, Char, String.to_list(D2.spell(ps) ++ "\""),
            '"' <> List.append(&2, Char, w, acc)), '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w, acc)), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps) ++ "\""), '"' <> List.append(&2, Char, w, acc)), List.reverse.go(&2, Char,
            String.to_list("\""), List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2,
            Char, w, acc))), '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2,
            Char, w, acc)), srev_app(D2.spell(ps), "\"", '"' <> List.append(&2, Char, w, acc)), {==})))))))))))))
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JArr{V.JNull{}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JArr{V.JBool{+x1}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JArr{V.JNum{+x1}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JArr{V.JStr{+x1}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JArr{V.JArr{+x1}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JArr{V.JObj{+x1}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JArr{V.JNil{}}:
      match sh:
        case V.WVal{}:
          use_p(bldg(V.WVal{}, fits, rr, acc), fits, Lex.TCloseArr{} <> rr, acc, '[', take_oa(fits,
            Lex.TCloseArr{} <> rr, acc, ht, ho), +w => +f1 => t1 => o1 => a1 => e1 => use_p(bldg(V.WVal{}, fits, rr,
            acc), f1, rr, '[' <> List.append(&2, Char, w, acc), ']', take_ca(f1, rr, '[' <> List.append(&2, Char, w,
            acc), t1, o1), +w0 => +f2 => t2 => o2 => a2 => e2 => (w, (D2.GArr0{Lex.text(w0)}, (f2, (t2, (o2, (a1,
            (aw_text(w0, "", a2, {==}), Equal.trans(List<&2, Char>, M6.fr(fits, acc), M6.fr(f1, '[' <> List.append(&2,
                Char,
            w, acc)), M6.fr(f2, List.reverse.go(&2, Char, String.to_list("[" ++ Lex.text(w0) ++ "]"), List.append(&2,
            Char, w, acc))), e1, Equal.trans(List<&2, Char>, M6.fr(f1, '[' <> List.append(&2, Char, w, acc)), M6.fr(f2,
            ']' <> List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc))), M6.fr(f2, List.reverse.go(&2, Char,
            String.to_list("[" ++ Lex.text(w0) ++ "]"), List.append(&2, Char, w, acc))), e2, Equal.cong(List<&2, Char>,
            List<&2, Char>, zz => M6.fr(f2, zz), ']' <> List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char, String.to_list("[" ++ Lex.text(w0) ++ "]"), List.append(&2, Char, w, acc)),
            Equal.sym(List<&2, Char>, List.reverse.go(&2, Char, String.to_list("[" ++ Lex.text(w0) ++ "]"),
            List.append(&2, Char, w, acc)), ']' <> List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc)),
            Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list("[" ++ Lex.text(w0) ++ "]"),
            List.append(&2, Char, w, acc)), List.reverse.go(&2, Char, String.to_list(Lex.text(w0) ++ "]"),
            '[' <> List.append(&2, Char, w, acc)), ']' <> List.append(&2, Char, w0, '[' <> List.append(&2, Char, w,
            acc)), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list(Lex.text(w0) ++ "]"),
            '[' <> List.append(&2, Char, w, acc)), List.reverse.go(&2, Char, String.to_list("]"), List.reverse.go(&2,
            Char, String.to_list(Lex.text(w0)), '[' <> List.append(&2, Char, w, acc))), ']' <> List.append(&2, Char,
            w0, '[' <> List.append(&2, Char, w, acc)), srev_app(Lex.text(w0), "]", '[' <> List.append(&2, Char, w,
            acc)), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list("]"), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0)), '[' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char,
            String.to_list("]"), List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc))),
            ']' <> List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc)), Equal.cong(List<&2, Char>, List<&2,
            Char>, zz => List.reverse.go(&2, Char, String.to_list("]"), zz), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0)), '[' <> List.append(&2, Char, w, acc)), List.append(&2, Char, w0,
            '[' <> List.append(&2, Char, w, acc)), text_rc(w0, "", '[' <> List.append(&2, Char, w, acc))),
            {==}))))))))))))))))
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JArr{V.JCons{+x1, +x2}}:
      match sh:
        case V.WVal{}:
          use_p(bldg(V.WVal{}, fits, rr, acc), fits, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok,
              M13.tj_r(V.JCons{x1,
            x2}, V.WArr{}), [Lex.TCloseArr{}]), rr), acc, '[', take_oa(fits, List.append(&2, Lex.Tok, List.append(&2,
            Lex.Tok, M13.tj_r(V.JCons{x1, x2}, V.WArr{}), [Lex.TCloseArr{}]), rr), acc, ht, ho),
            +w => +f1 => t1 => o1 => a1 => e1 => use_bv(bldg(V.WVal{}, fits, rr, acc), f1, List.append(&2, Lex.Tok,
            ctk(x2), Lex.TCloseArr{} <> rr), '[' <> List.append(&2, Char, w, acc), bld(x1, V.WVal{}, f1,
            List.append(&2, Lex.Tok, ctk(x2), Lex.TCloseArr{} <> rr), '[' <> List.append(&2, Char, w, acc),
            M6.stop_l(V.wf(x1), V.wf.go(x2, V.WArr{}), hw), Equal.trans(List<&2, Lex.Tok>, M6.dens(M13.rtoks(f1)),
            List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(V.JCons{x1, x2}, V.WArr{}), [Lex.TCloseArr{}]),
                rr),
            List.append(&2, Lex.Tok, M13.tj_r(x1, V.WVal{}), List.append(&2, Lex.Tok, ctk(x2), Lex.TCloseArr{} <> rr)),
                t1,
            Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(V.JCons{x1, x2},
            V.WArr{}), [Lex.TCloseArr{}]), rr), List.append(&2, Lex.Tok, M13.tj_r(V.JCons{x1, x2}, V.WArr{}),
            Lex.TCloseArr{} <> rr), List.append(&2, Lex.Tok, M13.tj_r(x1, V.WVal{}), List.append(&2, Lex.Tok, ctk(x2),
            Lex.TCloseArr{} <> rr)), M9.lapp_assoc(M13.tj_r(V.JCons{x1, x2}, V.WArr{}), [Lex.TCloseArr{}], rr),
                ctoks(x1, x2,
            Lex.TCloseArr{} <> rr))), o1), +w0 => +g1 => +f2 => t2 => o2 => a2 => k2 => e2 => use_ba(bldg(V.WVal{},
            fits, rr, acc), f2, rr, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char,
            w0, '[' <> List.append(&2, Char, w, acc))), bld(x2, V.WArr{}, f2, rr, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc))),
            M6.stop_r(V.wf(x1), V.wf.go(x2, V.WArr{}), hw), t2, o2),
            +w1 => +gc => +f3 => t3 => o3 => a3 => k3 => e3 => (w, (D2.GArr{Lex.text(w0), g1, Lex.text(w1), gc}, (f3,
            (t3, (o3, (a1, (M6.and2(D1.all_ws(Lex.text(w0)), Bool.and(D2.g.ok(g1, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w1)), D2.g.ok(gc, D2.GKArr{}))), aw_text(w0, "", a2, {==}),
            M6.and2(D2.g.ok(g1, D2.GKVal{}), Bool.and(D1.all_ws(Lex.text(w1)), D2.g.ok(gc, D2.GKArr{})), k2,
            M6.and2(D1.all_ws(Lex.text(w1)), D2.g.ok(gc, D2.GKArr{}), aw_text(w1, "", a3, {==}), k3))),
            Equal.trans(List<&2, Char>, M6.fr(fits, acc), M6.fr(f1, '[' <> List.append(&2, Char, w, acc)), M6.fr(f3,
            List.reverse.go(&2, Char,
            String.to_list("[" ++ Lex.text(w0) ++ D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"),
            List.append(&2, Char, w, acc))), e1, Equal.trans(List<&2, Char>, M6.fr(f1, '[' <> List.append(&2, Char, w,
            acc)), M6.fr(f2, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w0,
            '[' <> List.append(&2, Char, w, acc)))), M6.fr(f3, List.reverse.go(&2, Char,
            String.to_list("[" ++ Lex.text(w0) ++ D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"),
            List.append(&2, Char, w, acc))), e2, Equal.trans(List<&2, Char>, M6.fr(f2, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc)))), M6.fr(f3,
            ']' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w1,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2,
            Char, w, acc)))))), M6.fr(f3, List.reverse.go(&2, Char,
            String.to_list("[" ++ Lex.text(w0) ++ D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"),
            List.append(&2, Char, w, acc))), e3, Equal.cong(List<&2, Char>, List<&2, Char>, zz => M6.fr(f3, zz),
            ']' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w1,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2,
            Char, w, acc))))), List.reverse.go(&2, Char,
            String.to_list("[" ++ Lex.text(w0) ++ D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"),
            List.append(&2, Char, w, acc)), Equal.sym(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("[" ++ Lex.text(w0) ++ D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"),
            List.append(&2, Char, w, acc)), ']' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)),
            List.append(&2, Char, w1, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char,
            w0, '[' <> List.append(&2, Char, w, acc))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("[" ++ Lex.text(w0) ++ D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"),
            List.append(&2, Char, w, acc)), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0) ++ D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"),
            '[' <> List.append(&2, Char, w, acc)), ']' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)),
            List.append(&2, Char, w1, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char,
            w0, '[' <> List.append(&2, Char, w, acc))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0) ++ D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"),
            '[' <> List.append(&2, Char, w, acc)), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0)), '[' <> List.append(&2, Char, w, acc))), ']' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w1, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc))))),
            srev_app(Lex.text(w0), D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]", '[' <> List.append(&2,
            Char, w, acc)), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0)), '[' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"), List.append(&2, Char, w0,
            '[' <> List.append(&2, Char, w, acc))), ']' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)),
            List.append(&2, Char, w1, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char,
            w0, '[' <> List.append(&2, Char, w, acc))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char, String.to_list(D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"),
            zz), List.reverse.go(&2, Char, String.to_list(Lex.text(w0)), '[' <> List.append(&2, Char, w, acc)),
            List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc)), text_rc(w0, "", '[' <> List.append(&2,
            Char, w, acc))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1) ++ Lex.text(w1) ++ D2.g.text(gc) ++ "]"), List.append(&2, Char, w0,
            '[' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1) ++ D2.g.text(gc) ++ "]"), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc)))),
            ']' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w1,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2,
            Char, w, acc))))), srev_app(D2.g.text(g1), Lex.text(w1) ++ D2.g.text(gc) ++ "]", List.append(&2, Char,
            w0, '[' <> List.append(&2, Char, w, acc))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1) ++ D2.g.text(gc) ++ "]"), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc)))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gc) ++ "]"), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1)), List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2,
            Char, w0, '[' <> List.append(&2, Char, w, acc))))), ']' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w1, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc))))),
            srev_app(Lex.text(w1), D2.g.text(gc) ++ "]", List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)),
            List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc)))), Equal.trans(List<&2, Char>,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gc) ++ "]"), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1)), List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2,
            Char, w0, '[' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc) ++ "]"), List.append(&2, Char, w1, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc))))),
            ']' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w1,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2,
            Char, w, acc))))), Equal.cong(List<&2, Char>, List<&2, Char>, zz => List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc) ++ "]"), zz), List.reverse.go(&2, Char, String.to_list(Lex.text(w1)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2,
            Char, w, acc)))), List.append(&2, Char, w1, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)),
            List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc)))), text_rc(w1, "", List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc))))),
            Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list(D2.g.text(gc) ++ "]"),
            List.append(&2, Char, w1, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char,
            w0, '[' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char, String.to_list("]"),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w1, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc)))))),
            ']' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w1,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2,
            Char, w, acc))))), srev_app(D2.g.text(gc), "]", List.append(&2, Char, w1, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w0, '[' <> List.append(&2, Char, w, acc))))),
            {==}))))))))))))))))))))))
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JArr{V.JPair{+x1, +x2, +x3}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JArr{V.JSpan{+x1, +x2}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JArr{V.JBind{+x1, +x2, +x3, +x4}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JObj{V.JNull{}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JObj{V.JBool{+x1}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JObj{V.JNum{+x1}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JObj{V.JStr{+x1}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JObj{V.JArr{+x1}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JObj{V.JObj{+x1}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JObj{V.JNil{}}:
      match sh:
        case V.WVal{}:
          use_p(bldg(V.WVal{}, fits, rr, acc), fits, Lex.TCloseObj{} <> rr, acc, '{', take_oo(fits,
            Lex.TCloseObj{} <> rr, acc, ht, ho), +w => +f1 => t1 => o1 => a1 => e1 => use_p(bldg(V.WVal{}, fits, rr,
            acc), f1, rr, '{' <> List.append(&2, Char, w, acc), '}', take_co(f1, rr, '{' <> List.append(&2, Char, w,
            acc), t1, o1), +w0 => +f2 => t2 => o2 => a2 => e2 => (w, (D2.GObj0{Lex.text(w0)}, (f2, (t2, (o2, (a1,
            (aw_text(w0, "", a2, {==}), Equal.trans(List<&2, Char>, M6.fr(fits, acc), M6.fr(f1, '{' <> List.append(&2,
                Char,
            w, acc)), M6.fr(f2, List.reverse.go(&2, Char, String.to_list("{" ++ Lex.text(w0) ++ "}"), List.append(&2,
            Char, w, acc))), e1, Equal.trans(List<&2, Char>, M6.fr(f1, '{' <> List.append(&2, Char, w, acc)), M6.fr(f2,
            '}' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))), M6.fr(f2, List.reverse.go(&2, Char,
            String.to_list("{" ++ Lex.text(w0) ++ "}"), List.append(&2, Char, w, acc))), e2, Equal.cong(List<&2, Char>,
            List<&2, Char>, zz => M6.fr(f2, zz), '}' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char, String.to_list("{" ++ Lex.text(w0) ++ "}"), List.append(&2, Char, w, acc)),
            Equal.sym(List<&2, Char>, List.reverse.go(&2, Char, String.to_list("{" ++ Lex.text(w0) ++ "}"),
            List.append(&2, Char, w, acc)), '}' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)),
            Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list("{" ++ Lex.text(w0) ++ "}"),
            List.append(&2, Char, w, acc)), List.reverse.go(&2, Char, String.to_list(Lex.text(w0) ++ "}"),
            '{' <> List.append(&2, Char, w, acc)), '}' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w,
            acc)), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list(Lex.text(w0) ++ "}"),
            '{' <> List.append(&2, Char, w, acc)), List.reverse.go(&2, Char, String.to_list("}"), List.reverse.go(&2,
            Char, String.to_list(Lex.text(w0)), '{' <> List.append(&2, Char, w, acc))), '}' <> List.append(&2, Char,
            w0, '{' <> List.append(&2, Char, w, acc)), srev_app(Lex.text(w0), "}", '{' <> List.append(&2, Char, w,
            acc)), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list("}"), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0)), '{' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char,
            String.to_list("}"), List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))),
            '}' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)), Equal.cong(List<&2, Char>, List<&2,
            Char>, zz => List.reverse.go(&2, Char, String.to_list("}"), zz), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0)), '{' <> List.append(&2, Char, w, acc)), List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)), text_rc(w0, "", '{' <> List.append(&2, Char, w, acc))),
            {==}))))))))))))))))
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JObj{V.JCons{+x1, +x2}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JObj{V.JPair{+x1, +x2, +x3}}:
      match sh:
        case V.WVal{}:
          use_p(bldg(V.WVal{}, fits, rr, acc), fits, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok,
              M13.tj_r(V.JPair{x1,
            x2, x3}, V.WObj{}), [Lex.TCloseObj{}]), rr), acc, '{', take_oo(fits, List.append(&2, Lex.Tok,
            List.append(&2, Lex.Tok, M13.tj_r(V.JPair{x1, x2, x3}, V.WObj{}), [Lex.TCloseObj{}]), rr), acc, ht, ho),
            +w => +f1 => t1 => o1 => a1 => e1 => use_s(bldg(V.WVal{}, fits, rr, acc), f1, x1,
            Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}), List.append(&2, Lex.Tok, otk(x3),
            Lex.TCloseObj{} <> rr)), '{' <> List.append(&2, Char, w, acc), take_s(f1, x1,
            Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}), List.append(&2, Lex.Tok, otk(x3),
            Lex.TCloseObj{} <> rr)), '{' <> List.append(&2, Char, w, acc), Equal.trans(List<&2, Lex.Tok>,
            M6.dens(M13.rtoks(f1)), List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(V.JPair{x1, x2, x3},
                V.WObj{}),
            [Lex.TCloseObj{}]), rr), Lex.TStr{x1} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}),
            List.append(&2, Lex.Tok, otk(x3), Lex.TCloseObj{} <> rr)), t1, Equal.trans(List<&2, Lex.Tok>,
            List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(V.JPair{x1, x2, x3}, V.WObj{}),
                [Lex.TCloseObj{}]),
            rr), List.append(&2, Lex.Tok, M13.tj_r(V.JPair{x1, x2, x3}, V.WObj{}), Lex.TCloseObj{} <> rr),
            Lex.TStr{x1} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}), List.append(&2, Lex.Tok,
            otk(x3), Lex.TCloseObj{} <> rr)), M9.lapp_assoc(M13.tj_r(V.JPair{x1, x2, x3}, V.WObj{}), [Lex.TCloseObj{}],
                rr),
            ptoks(x1, x2, x3, Lex.TCloseObj{} <> rr))), o1),
            +w0 => +ps => +f2 => t2 => o2 => a2 => okp => _esp => e2 => use_p(bldg(V.WVal{}, fits, rr, acc), f2,
            List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}), List.append(&2, Lex.Tok, otk(x3), Lex.TCloseObj{} <> rr)),
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))), ':', take_col(f2, List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}),
            List.append(&2, Lex.Tok, otk(x3), Lex.TCloseObj{} <> rr)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))),
            t2, o2), +w1 => +f3 => t3 => o3 => a3 => e3 => use_bv(bldg(V.WVal{}, fits, rr, acc), f3, List.append(&2,
            Lex.Tok, otk(x3), Lex.TCloseObj{} <> rr), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))),
            bld(x2, V.WVal{}, f3, List.append(&2, Lex.Tok, otk(x3), Lex.TCloseObj{} <> rr), ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))), M6.stop_l(V.wf(x2), V.wf.go(x3, V.WObj{}), hw), t3, o3),
            +w2 => +g1 => +f4 => t4 => o4 => a4 => k4 => e4 => use_bo(bldg(V.WVal{}, fits, rr, acc), f4, rr,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))), bld(x3, V.WObj{}, f4, rr, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))), M6.stop_r(V.wf(x2), V.wf.go(x3, V.WObj{}), hw), t4, o4),
            +w3 => +gc => +f5 => t5 => o5 => a5 => k5 => e5 => (w, (D2.GObj{Lex.text(w0), ps, Lex.text(w1),
            Lex.text(w2), g1, Lex.text(w3), gc}, (f5, (t5, (o5, (a1, (M6.and2(D1.all_ws(Lex.text(w0)),
            Bool.and(D2.spell_ok(ps), Bool.and(D1.all_ws(Lex.text(w1)), Bool.and(D1.all_ws(Lex.text(w2)),
            Bool.and(D2.g.ok(g1, D2.GKVal{}), Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gc, D2.GKObj{})))))),
            aw_text(w0, "", a2, {==}), M6.and2(D2.spell_ok(ps), Bool.and(D1.all_ws(Lex.text(w1)),
            Bool.and(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g1, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gc, D2.GKObj{}))))), okp, M6.and2(D1.all_ws(Lex.text(w1)),
            Bool.and(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g1, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gc, D2.GKObj{})))), aw_text(w1, "", a3, {==}),
            M6.and2(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g1, D2.GKVal{}), Bool.and(D1.all_ws(Lex.text(w3)),
            D2.g.ok(gc, D2.GKObj{}))), aw_text(w2, "", a4, {==}), M6.and2(D2.g.ok(g1, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gc, D2.GKObj{})), k4, M6.and2(D1.all_ws(Lex.text(w3)),
            D2.g.ok(gc, D2.GKObj{}), aw_text(w3, "", a5, {==}), k5)))))), Equal.trans(List<&2, Char>, M6.fr(fits,
            acc), M6.fr(f1, '{' <> List.append(&2, Char, w, acc)), M6.fr(f5, List.reverse.go(&2, Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w,
            acc))), e1, Equal.trans(List<&2, Char>, M6.fr(f1, '{' <> List.append(&2, Char, w, acc)), M6.fr(f2,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))), M6.fr(f5, List.reverse.go(&2, Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w,
            acc))), e2, Equal.trans(List<&2, Char>, M6.fr(f2, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))),
            M6.fr(f3, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))), M6.fr(f5, List.reverse.go(&2,
                Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w,
            acc))), e3, Equal.trans(List<&2, Char>, M6.fr(f3, ':' <> List.append(&2, Char, w1,
                '"' <> List.reverse.go(&2,
            Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w,
            acc))))), M6.fr(f4, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))))), M6.fr(f5, List.reverse.go(&2,
            Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w,
            acc))), e4, Equal.trans(List<&2, Char>, M6.fr(f4, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w,
            acc))))))), M6.fr(f5, '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char,
            w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))))))), M6.fr(f5, List.reverse.go(&2,
            Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w,
            acc))), e5, Equal.cong(List<&2, Char>, List<&2, Char>, zz => M6.fr(f5, zz), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), List.reverse.go(&2, Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w, acc)),
            Equal.sym(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w, acc)),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++
            D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), '{' <> List.append(&2, Char, w, acc)),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++
            D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), '{' <> List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(Lex.text(w0)),
            '{' <> List.append(&2, Char, w, acc))), '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w0),
            "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++
            D2.g.text(gc) ++ "}", '{' <> List.append(&2, Char, w, acc)), Equal.trans(List<&2, Char>,
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(Lex.text(w0)),
            '{' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), zz), List.reverse.go(&2, Char, String.to_list(Lex.text(w0)),
            '{' <> List.append(&2, Char, w, acc)), List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)),
            text_rc(w0, "", '{' <> List.append(&2, Char, w, acc))), Equal.trans(List<&2, Char>, List.reverse.go(&2,
            Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))),
            List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w,
            acc))), '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w,
            acc))), List.reverse.go(&2, Char,
            String.to_list("\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++
            D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2,
            Char, w0, '{' <> List.append(&2, Char, w, acc)))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(D2.spell(ps),
            "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}",
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))), Equal.trans(List<&2, Char>,
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++
            D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2,
            Char, w0, '{' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++
            "}"), '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))), '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2,
            Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++
            "}"), '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w1),
            ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}",
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))),
            List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), zz),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))),
            List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))), text_rc(w1, "",
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w2),
            D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}", ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char, String.to_list(D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            zz), List.reverse.go(&2, Char, String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))), text_rc(w2, "", ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(D2.g.text(g1),
            Lex.text(w3) ++ D2.g.text(gc) ++ "}", List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(Lex.text(w3)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w3), D2.g.text(gc) ++ "}",
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(Lex.text(w3)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc) ++ "}"), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char, String.to_list(D2.g.text(gc) ++ "}"), zz), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w3)), List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2,
            Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))))), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))))), text_rc(w3, "", List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc) ++ "}"), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), List.reverse.go(&2, Char, String.to_list("}"),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(D2.g.text(gc), "}", List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), {==}))))))))))))))))))))))))))))))))))
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JObj{V.JSpan{+x1, +x2}}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JObj{V.JBind{+x1, +x2, +x3, +x4}}:
      match sh:
        case V.WVal{}:
          use_p(bldg(V.WVal{}, fits, rr, acc), fits, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok,
              M13.tj_r(V.JBind{x1,
            x2, x3, x4}, V.WObj{}), [Lex.TCloseObj{}]), rr), acc, '{', take_oo(fits, List.append(&2, Lex.Tok,
            List.append(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{}), [Lex.TCloseObj{}]), rr), acc, ht, ho),
            +w => +f1 => t1 => o1 => a1 => e1 => use_s(bldg(V.WVal{}, fits, rr, acc), f1, V.span.str(x1, x2,
            U32.is_zero(x2)), Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x3, V.WVal{}), List.append(&2, Lex.Tok,
            otk(x4), Lex.TCloseObj{} <> rr)), '{' <> List.append(&2, Char, w, acc), take_s(f1, V.span.str(x1, x2,
            U32.is_zero(x2)), Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x3, V.WVal{}), List.append(&2, Lex.Tok,
            otk(x4), Lex.TCloseObj{} <> rr)), '{' <> List.append(&2, Char, w, acc), Equal.trans(List<&2, Lex.Tok>,
            M6.dens(M13.rtoks(f1)), List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2, x3, x4},
                V.WObj{}),
            [Lex.TCloseObj{}]), rr), Lex.TStr{V.span.str(x1, x2, U32.is_zero(x2))} <> Lex.TColon{} <> List.append(&2,
            Lex.Tok, M13.tj_r(x3, V.WVal{}), List.append(&2, Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr)), t1,
            Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2,
                x3,
            x4}, V.WObj{}), [Lex.TCloseObj{}]), rr), List.append(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2, x3, x4},
                V.WObj{}),
            Lex.TCloseObj{} <> rr), Lex.TStr{V.span.str(x1, x2, U32.is_zero(x2))} <> Lex.TColon{} <> List.append(&2,
            Lex.Tok, M13.tj_r(x3, V.WVal{}), List.append(&2, Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr)),
            M9.lapp_assoc(M13.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{}), [Lex.TCloseObj{}], rr), btoks(x1, x2, x3, x4,
            Lex.TCloseObj{} <> rr))), o1),
            +w0 => +ps => +f2 => t2 => o2 => a2 => okp => _esp => e2 => use_p(bldg(V.WVal{}, fits, rr, acc), f2,
            List.append(&2, Lex.Tok, M13.tj_r(x3, V.WVal{}), List.append(&2, Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr)),
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))), ':', take_col(f2, List.append(&2, Lex.Tok, M13.tj_r(x3, V.WVal{}),
            List.append(&2, Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))),
            t2, o2), +w1 => +f3 => t3 => o3 => a3 => e3 => use_bv(bldg(V.WVal{}, fits, rr, acc), f3, List.append(&2,
            Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))),
            bld(x3, V.WVal{}, f3, List.append(&2, Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr), ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))), M6.stop_l(V.wf(x3), V.wf.go(x4, V.WObj{}), hw), t3, o3),
            +w2 => +g1 => +f4 => t4 => o4 => a4 => k4 => e4 => use_bo(bldg(V.WVal{}, fits, rr, acc), f4, rr,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))), bld(x4, V.WObj{}, f4, rr, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))), M6.stop_r(V.wf(x3), V.wf.go(x4, V.WObj{}), hw), t4, o4),
            +w3 => +gc => +f5 => t5 => o5 => a5 => k5 => e5 => (w, (D2.GObj{Lex.text(w0), ps, Lex.text(w1),
            Lex.text(w2), g1, Lex.text(w3), gc}, (f5, (t5, (o5, (a1, (M6.and2(D1.all_ws(Lex.text(w0)),
            Bool.and(D2.spell_ok(ps), Bool.and(D1.all_ws(Lex.text(w1)), Bool.and(D1.all_ws(Lex.text(w2)),
            Bool.and(D2.g.ok(g1, D2.GKVal{}), Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gc, D2.GKObj{})))))),
            aw_text(w0, "", a2, {==}), M6.and2(D2.spell_ok(ps), Bool.and(D1.all_ws(Lex.text(w1)),
            Bool.and(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g1, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gc, D2.GKObj{}))))), okp, M6.and2(D1.all_ws(Lex.text(w1)),
            Bool.and(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g1, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gc, D2.GKObj{})))), aw_text(w1, "", a3, {==}),
            M6.and2(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g1, D2.GKVal{}), Bool.and(D1.all_ws(Lex.text(w3)),
            D2.g.ok(gc, D2.GKObj{}))), aw_text(w2, "", a4, {==}), M6.and2(D2.g.ok(g1, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gc, D2.GKObj{})), k4, M6.and2(D1.all_ws(Lex.text(w3)),
            D2.g.ok(gc, D2.GKObj{}), aw_text(w3, "", a5, {==}), k5)))))), Equal.trans(List<&2, Char>, M6.fr(fits,
            acc), M6.fr(f1, '{' <> List.append(&2, Char, w, acc)), M6.fr(f5, List.reverse.go(&2, Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w,
            acc))), e1, Equal.trans(List<&2, Char>, M6.fr(f1, '{' <> List.append(&2, Char, w, acc)), M6.fr(f2,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))), M6.fr(f5, List.reverse.go(&2, Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w,
            acc))), e2, Equal.trans(List<&2, Char>, M6.fr(f2, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))),
            M6.fr(f3, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))), M6.fr(f5, List.reverse.go(&2,
                Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w,
            acc))), e3, Equal.trans(List<&2, Char>, M6.fr(f3, ':' <> List.append(&2, Char, w1,
                '"' <> List.reverse.go(&2,
            Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w,
            acc))))), M6.fr(f4, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))))), M6.fr(f5, List.reverse.go(&2,
            Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w,
            acc))), e4, Equal.trans(List<&2, Char>, M6.fr(f4, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w,
            acc))))))), M6.fr(f5, '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char,
            w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))))))), M6.fr(f5, List.reverse.go(&2,
            Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w,
            acc))), e5, Equal.cong(List<&2, Char>, List<&2, Char>, zz => M6.fr(f5, zz), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), List.reverse.go(&2, Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w, acc)),
            Equal.sym(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w, acc)),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("{" ++ Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++
            D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), '{' <> List.append(&2, Char, w, acc)),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w0) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++
            D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), '{' <> List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(Lex.text(w0)),
            '{' <> List.append(&2, Char, w, acc))), '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w0),
            "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++
            D2.g.text(gc) ++ "}", '{' <> List.append(&2, Char, w, acc)), Equal.trans(List<&2, Char>,
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(Lex.text(w0)),
            '{' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), zz), List.reverse.go(&2, Char, String.to_list(Lex.text(w0)),
            '{' <> List.append(&2, Char, w, acc)), List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)),
            text_rc(w0, "", '{' <> List.append(&2, Char, w, acc))), Equal.trans(List<&2, Char>, List.reverse.go(&2,
            Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))),
            List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w,
            acc))), '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++
            Lex.text(w3) ++ D2.g.text(gc) ++ "}"), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w,
            acc))), List.reverse.go(&2, Char,
            String.to_list("\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++
            D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2,
            Char, w0, '{' <> List.append(&2, Char, w, acc)))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(D2.spell(ps),
            "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}",
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))), Equal.trans(List<&2, Char>,
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++
            D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2,
            Char, w0, '{' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++
            "}"), '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))), '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2,
            Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++
            "}"), '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w1),
            ":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}",
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))),
            List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), zz),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))),
            List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))), text_rc(w1, "",
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2) ++ D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w2),
            D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}", ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))),
            '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char, String.to_list(D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"),
            zz), List.reverse.go(&2, Char, String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))), text_rc(w2, "", ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1) ++ Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc)))))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(D2.g.text(g1),
            Lex.text(w3) ++ D2.g.text(gc) ++ "}", List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w3) ++ D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(Lex.text(w3)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w3), D2.g.text(gc) ++ "}",
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc) ++ "}"), List.reverse.go(&2, Char, String.to_list(Lex.text(w3)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc) ++ "}"), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char, String.to_list(D2.g.text(gc) ++ "}"), zz), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w3)), List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2,
            Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w0, '{' <> List.append(&2, Char, w, acc))))))), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))))), text_rc(w3, "", List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc) ++ "}"), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), List.reverse.go(&2, Char, String.to_list("}"),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc))))))))), '}' <> List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gc)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), srev_app(D2.g.text(gc), "}", List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g1)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w0,
            '{' <> List.append(&2, Char, w, acc)))))))), {==}))))))))))))))))))))))))))))))))))
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          use_p(bldg(V.WArr{}, fits, rr, acc), fits, rr, acc, ']', take_ca(fits, rr, acc, ht, ho),
            +w => +f1 => t1 => o1 => a1 => e1 => (w, (D2.GEnd{}, (f1, (t1, (o1, (a1, ({==}, e1))))))))
        case V.WObj{}:
          use_p(bldg(V.WObj{}, fits, rr, acc), fits, rr, acc, '}', take_co(fits, rr, acc, ht, ho),
            +w => +f1 => t1 => o1 => a1 => e1 => (w, (D2.GEnd{}, (f1, (t1, (o1, (a1, ({==}, e1))))))))
    case V.JCons{+x1, +x2}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          use_p(bldg(V.WArr{}, fits, rr, acc), fits, List.append(&2, Lex.Tok, M13.tj_r(V.JCons{x1, x2}, V.WArr{}),
            Lex.TCloseArr{} <> rr), acc, ',', take_com(fits, List.append(&2, Lex.Tok, M13.tj_r(V.JCons{x1, x2},
                V.WArr{}),
            Lex.TCloseArr{} <> rr), acc, ht, ho), +w => +f1 => t1 => o1 => a1 => e1 => use_bv(bldg(V.WArr{}, fits, rr,
            acc), f1, List.append(&2, Lex.Tok, ctk(x2), Lex.TCloseArr{} <> rr), ',' <> List.append(&2, Char, w, acc),
            bld(x1, V.WVal{}, f1, List.append(&2, Lex.Tok, ctk(x2), Lex.TCloseArr{} <> rr), ',' <> List.append(&2,
            Char, w, acc), M6.stop_l(V.wf(x1), V.wf.go(x2, V.WArr{}), hw), Equal.trans(List<&2, Lex.Tok>,
                M6.dens(M13.rtoks(f1)),
            List.append(&2, Lex.Tok, M13.tj_r(V.JCons{x1, x2}, V.WArr{}), Lex.TCloseArr{} <> rr), List.append(&2,
                Lex.Tok,
            M13.tj_r(x1, V.WVal{}), List.append(&2, Lex.Tok, ctk(x2), Lex.TCloseArr{} <> rr)), t1, ctoks(x1, x2,
            Lex.TCloseArr{} <> rr)), o1), +w2 => +g2 => +f2 => t2 => o2 => a2 => k2 => e2 => use_ba(bldg(V.WArr{},
            fits, rr, acc), f2, rr, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ',' <> List.append(&2, Char, w, acc))), bld(x2, V.WArr{}, f2, rr, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2, Char, w, acc))),
            M6.stop_r(V.wf(x1), V.wf.go(x2, V.WArr{}), hw), t2, o2),
            +wb => +gr => +f3 => t3 => o3 => a3 => k3 => e3 => (w, (D2.GNext{Lex.text(w2), g2, Lex.text(wb), gr},
            (f3, (t3, (o3, (a1, (M6.and2(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g2, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(wb)), D2.g.ok(gr, D2.GKArr{}))), aw_text(w2, "", a2, {==}),
            M6.and2(D2.g.ok(g2, D2.GKVal{}), Bool.and(D1.all_ws(Lex.text(wb)), D2.g.ok(gr, D2.GKArr{})), k2,
            M6.and2(D1.all_ws(Lex.text(wb)), D2.g.ok(gr, D2.GKArr{}), aw_text(wb, "", a3, {==}), k3))),
            Equal.trans(List<&2, Char>, M6.fr(fits, acc), M6.fr(f1, ',' <> List.append(&2, Char, w, acc)), M6.fr(f3,
            ']' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), List.append(&2,
            Char, w, acc))), e1, Equal.trans(List<&2, Char>, M6.fr(f1, ',' <> List.append(&2, Char, w, acc)), M6.fr(f2,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2,
            Char, w, acc)))), M6.fr(f3, ']' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), List.append(&2,
            Char, w, acc))), e2, Equal.trans(List<&2, Char>, M6.fr(f2, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2, Char, w, acc)))), M6.fr(f3,
            ']' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, wb,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2,
            Char, w, acc)))))), M6.fr(f3, ']' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), List.append(&2,
            Char, w, acc))), e3, Equal.cong(List<&2, Char>, List<&2, Char>, zz => M6.fr(f3, ']' <> zz),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, wb, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2, Char, w, acc))))),
            List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), List.append(&2,
            Char, w, acc)), Equal.sym(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), List.append(&2,
            Char, w, acc)), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, wb,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2,
            Char, w, acc))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), List.append(&2,
            Char, w, acc)), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), ',' <> List.append(&2,
            Char, w, acc)), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, wb,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2,
            Char, w, acc))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), ',' <> List.append(&2,
            Char, w, acc)), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2)), ',' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gr)), List.append(&2, Char, wb, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2, Char, w, acc))))),
            srev_app(Lex.text(w2), D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr), ',' <> List.append(&2, Char, w,
            acc)), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2)), ',' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), List.append(&2, Char, w2,
            ',' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, wb, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ',' <> List.append(&2, Char, w, acc))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char, String.to_list(D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), zz),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w2)), ',' <> List.append(&2, Char, w, acc)),
            List.append(&2, Char, w2, ',' <> List.append(&2, Char, w, acc)), text_rc(w2, "", ',' <> List.append(&2,
            Char, w, acc))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2) ++ Lex.text(wb) ++ D2.g.text(gr)), List.append(&2, Char, w2,
            ',' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(wb) ++ D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)),
            List.append(&2, Char, w2, ',' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gr)), List.append(&2, Char, wb, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2, Char, w, acc))))),
            srev_app(D2.g.text(g2), Lex.text(wb) ++ D2.g.text(gr), List.append(&2, Char, w2, ',' <> List.append(&2,
            Char, w, acc))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(wb) ++ D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)),
            List.append(&2, Char, w2, ',' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(Lex.text(wb)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2,
            Char, w, acc))))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, wb,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2,
            Char, w, acc))))), srev_app(Lex.text(wb), D2.g.text(gr), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2, Char, w, acc)))),
            Equal.cong(List<&2, Char>, List<&2, Char>, zz => List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            zz), List.reverse.go(&2, Char, String.to_list(Lex.text(wb)), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2, Char, w, acc)))),
            List.append(&2, Char, wb, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ',' <> List.append(&2, Char, w, acc)))), text_rc(wb, "", List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ',' <> List.append(&2, Char, w,
            acc)))))))))))))))))))))))))
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JPair{+x1, +x2, +x3}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          use_p(bldg(V.WObj{}, fits, rr, acc), fits, List.append(&2, Lex.Tok, M13.tj_r(V.JPair{x1, x2, x3}, V.WObj{}),
            Lex.TCloseObj{} <> rr), acc, ',', take_com(fits, List.append(&2, Lex.Tok, M13.tj_r(V.JPair{x1, x2, x3},
            V.WObj{}), Lex.TCloseObj{} <> rr), acc, ht, ho), +w => +f1 => t1 => o1 => a1 => e1 => use_s(bldg(V.WObj{},
            fits, rr, acc), f1, x1, Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}), List.append(&2,
            Lex.Tok, otk(x3), Lex.TCloseObj{} <> rr)), ',' <> List.append(&2, Char, w, acc), take_s(f1, x1,
            Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}), List.append(&2, Lex.Tok, otk(x3),
            Lex.TCloseObj{} <> rr)), ',' <> List.append(&2, Char, w, acc), Equal.trans(List<&2, Lex.Tok>,
            M6.dens(M13.rtoks(f1)), List.append(&2, Lex.Tok, M13.tj_r(V.JPair{x1, x2, x3}, V.WObj{}),
                Lex.TCloseObj{} <> rr),
            Lex.TStr{x1} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}), List.append(&2, Lex.Tok,
            otk(x3), Lex.TCloseObj{} <> rr)), t1, ptoks(x1, x2, x3, Lex.TCloseObj{} <> rr)), o1),
            +w4 => +ps => +f2 => t2 => o2 => a2 => okp => _esp => e2 => use_p(bldg(V.WObj{}, fits, rr, acc), f2,
            List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}), List.append(&2, Lex.Tok, otk(x3), Lex.TCloseObj{} <> rr)),
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))), ':', take_col(f2, List.append(&2, Lex.Tok, M13.tj_r(x2, V.WVal{}),
            List.append(&2, Lex.Tok, otk(x3), Lex.TCloseObj{} <> rr)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))),
            t2, o2), +w1 => +f3 => t3 => o3 => a3 => e3 => use_bv(bldg(V.WObj{}, fits, rr, acc), f3, List.append(&2,
            Lex.Tok, otk(x3), Lex.TCloseObj{} <> rr), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))),
            bld(x2, V.WVal{}, f3, List.append(&2, Lex.Tok, otk(x3), Lex.TCloseObj{} <> rr), ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))), M6.stop_l(V.wf(x2), V.wf.go(x3, V.WObj{}), hw), t3, o3),
            +w2 => +g2 => +f4 => t4 => o4 => a4 => k4 => e4 => use_bo(bldg(V.WObj{}, fits, rr, acc), f4, rr,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))), bld(x3, V.WObj{}, f4, rr, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))), M6.stop_r(V.wf(x2), V.wf.go(x3, V.WObj{}), hw), t4, o4),
            +w3 => +gr => +f5 => t5 => o5 => a5 => k5 => e5 => (w, (D2.GNextM{Lex.text(w4), ps, Lex.text(w1),
            Lex.text(w2), g2, Lex.text(w3), gr}, (f5, (t5, (o5, (a1, (M6.and2(D1.all_ws(Lex.text(w4)),
            Bool.and(D2.spell_ok(ps), Bool.and(D1.all_ws(Lex.text(w1)), Bool.and(D1.all_ws(Lex.text(w2)),
            Bool.and(D2.g.ok(g2, D2.GKVal{}), Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gr, D2.GKObj{})))))),
            aw_text(w4, "", a2, {==}), M6.and2(D2.spell_ok(ps), Bool.and(D1.all_ws(Lex.text(w1)),
            Bool.and(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g2, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gr, D2.GKObj{}))))), okp, M6.and2(D1.all_ws(Lex.text(w1)),
            Bool.and(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g2, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gr, D2.GKObj{})))), aw_text(w1, "", a3, {==}),
            M6.and2(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g2, D2.GKVal{}), Bool.and(D1.all_ws(Lex.text(w3)),
            D2.g.ok(gr, D2.GKObj{}))), aw_text(w2, "", a4, {==}), M6.and2(D2.g.ok(g2, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gr, D2.GKObj{})), k4, M6.and2(D1.all_ws(Lex.text(w3)),
            D2.g.ok(gr, D2.GKObj{}), aw_text(w3, "", a5, {==}), k5)))))), Equal.trans(List<&2, Char>, M6.fr(fits,
            acc), M6.fr(f1, ',' <> List.append(&2, Char, w, acc)), M6.fr(f5, '}' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc))), e1,
            Equal.trans(List<&2, Char>, M6.fr(f1, ',' <> List.append(&2, Char, w, acc)), M6.fr(f2,
                '"' <> List.reverse.go(&2,
            Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w,
            acc)))), M6.fr(f5, '}' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc))), e2,
            Equal.trans(List<&2, Char>, M6.fr(f2, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))), M6.fr(f3, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), M6.fr(f5, '}' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc))), e3,
            Equal.trans(List<&2, Char>, M6.fr(f3, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))),
            M6.fr(f4, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))))), M6.fr(f5,
            '}' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc))), e4,
            Equal.trans(List<&2, Char>, M6.fr(f4, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w,
            acc))))))), M6.fr(f5, '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char,
            w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))))))), M6.fr(f5,
            '}' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc))), e5,
            Equal.cong(List<&2, Char>, List<&2, Char>, zz => M6.fr(f5, '}' <> zz), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc)),
            Equal.sym(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char,
            String.to_list(Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++
            D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), ',' <> List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++
            D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), ',' <> List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(Lex.text(w4)),
            ',' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w4),
            "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++
            D2.g.text(gr), ',' <> List.append(&2, Char, w, acc)), Equal.trans(List<&2, Char>, List.reverse.go(&2,
            Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(Lex.text(w4)),
            ',' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), zz), List.reverse.go(&2, Char, String.to_list(Lex.text(w4)),
            ',' <> List.append(&2, Char, w, acc)), List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)),
            text_rc(w4, "", ',' <> List.append(&2, Char, w, acc))), Equal.trans(List<&2, Char>, List.reverse.go(&2,
            Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))),
            List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))),
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++
            D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char,
            w4, ',' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), srev_app(D2.spell(ps),
            "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))), Equal.trans(List<&2, Char>,
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++
            D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char,
            w4, ',' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)),
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2,
            Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)),
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w1),
            ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))),
            Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))),
            List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>,
            List<&2, Char>, zz => List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), zz),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))),
            List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))), text_rc(w1, "",
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2,
            Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w2),
            D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr), ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char, String.to_list(D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), zz),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), text_rc(w2, "", ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w3) ++ D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w,
            acc))))))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), srev_app(D2.g.text(g2), Lex.text(w3) ++ D2.g.text(gr),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))),
            Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list(Lex.text(w3) ++ D2.g.text(gr)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w3)), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w3),
            D2.g.text(gr), List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))))), Equal.cong(List<&2, Char>,
            List<&2, Char>, zz => List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), zz), List.reverse.go(&2,
            Char, String.to_list(Lex.text(w3)), List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w,
            acc))))))), List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w,
            acc))))))), text_rc(w3, "", List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2,
            Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))))))))))))))))))))))))))))))))))))))
    case V.JSpan{+x1, +x2}:
      match sh:
        case V.WVal{}:
          use_s(bldg(V.WVal{}, fits, rr, acc), fits, V.span.str(x1, x2, U32.is_zero(x2)), rr, acc, take_s(fits,
            V.span.str(x1, x2, U32.is_zero(x2)), rr, acc, ht, ho),
            +w => +ps => +f1 => t1 => o1 => a1 => okp => _esp => e1 => (w, (D2.GStr{ps}, (f1, (t1, (o1, (a1, (okp,
            Equal.trans(List<&2, Char>, M6.fr(fits, acc), M6.fr(f1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w, acc))), M6.fr(f1, List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\""), List.append(&2, Char, w, acc))), e1, Equal.cong(List<&2,
            Char>, List<&2, Char>, zz => M6.fr(f1, zz), '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w, acc)), List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\""), List.append(&2, Char, w, acc)), Equal.sym(List<&2, Char>,
            List.reverse.go(&2, Char, String.to_list("\"" ++ D2.spell(ps) ++ "\""), List.append(&2, Char, w, acc)),
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w, acc)),
            Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list("\"" ++ D2.spell(ps) ++ "\""),
            List.append(&2, Char, w, acc)), List.reverse.go(&2, Char, String.to_list(D2.spell(ps) ++ "\""),
            '"' <> List.append(&2, Char, w, acc)), '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w, acc)), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps) ++ "\""), '"' <> List.append(&2, Char, w, acc)), List.reverse.go(&2, Char,
            String.to_list("\""), List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2,
            Char, w, acc))), '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2,
            Char, w, acc)), srev_app(D2.spell(ps), "\"", '"' <> List.append(&2, Char, w, acc)), {==})))))))))))))
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          M6.no(bldg(V.WObj{}, fits, rr, acc), hw)
    case V.JBind{+x1, +x2, +x3, +x4}:
      match sh:
        case V.WVal{}:
          M6.no(bldg(V.WVal{}, fits, rr, acc), hw)
        case V.WArr{}:
          M6.no(bldg(V.WArr{}, fits, rr, acc), hw)
        case V.WObj{}:
          use_p(bldg(V.WObj{}, fits, rr, acc), fits, List.append(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2, x3, x4},
              V.WObj{}),
            Lex.TCloseObj{} <> rr), acc, ',', take_com(fits, List.append(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2, x3, x4},
            V.WObj{}), Lex.TCloseObj{} <> rr), acc, ht, ho), +w => +f1 => t1 => o1 => a1 => e1 => use_s(bldg(V.WObj{},
            fits, rr, acc), f1, V.span.str(x1, x2, U32.is_zero(x2)), Lex.TColon{} <> List.append(&2, Lex.Tok,
                M13.tj_r(x3,
            V.WVal{}), List.append(&2, Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr)), ',' <> List.append(&2, Char, w, acc),
            take_s(f1, V.span.str(x1, x2, U32.is_zero(x2)), Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x3,
            V.WVal{}), List.append(&2, Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr)), ',' <> List.append(&2, Char, w, acc),
            Equal.trans(List<&2, Lex.Tok>, M6.dens(M13.rtoks(f1)), List.append(&2, Lex.Tok, M13.tj_r(V.JBind{x1, x2,
                x3, x4},
            V.WObj{}), Lex.TCloseObj{} <> rr), Lex.TStr{V.span.str(x1, x2,
            U32.is_zero(x2))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M13.tj_r(x3, V.WVal{}), List.append(&2,
                Lex.Tok,
            otk(x4), Lex.TCloseObj{} <> rr)), t1, btoks(x1, x2, x3, x4, Lex.TCloseObj{} <> rr)), o1),
            +w4 => +ps => +f2 => t2 => o2 => a2 => okp => _esp => e2 => use_p(bldg(V.WObj{}, fits, rr, acc), f2,
            List.append(&2, Lex.Tok, M13.tj_r(x3, V.WVal{}), List.append(&2, Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr)),
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))), ':', take_col(f2, List.append(&2, Lex.Tok, M13.tj_r(x3, V.WVal{}),
            List.append(&2, Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))),
            t2, o2), +w1 => +f3 => t3 => o3 => a3 => e3 => use_bv(bldg(V.WObj{}, fits, rr, acc), f3, List.append(&2,
            Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))),
            bld(x3, V.WVal{}, f3, List.append(&2, Lex.Tok, otk(x4), Lex.TCloseObj{} <> rr), ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))), M6.stop_l(V.wf(x3), V.wf.go(x4, V.WObj{}), hw), t3, o3),
            +w2 => +g2 => +f4 => t4 => o4 => a4 => k4 => e4 => use_bo(bldg(V.WObj{}, fits, rr, acc), f4, rr,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))), bld(x4, V.WObj{}, f4, rr, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))), M6.stop_r(V.wf(x3), V.wf.go(x4, V.WObj{}), hw), t4, o4),
            +w3 => +gr => +f5 => t5 => o5 => a5 => k5 => e5 => (w, (D2.GNextM{Lex.text(w4), ps, Lex.text(w1),
            Lex.text(w2), g2, Lex.text(w3), gr}, (f5, (t5, (o5, (a1, (M6.and2(D1.all_ws(Lex.text(w4)),
            Bool.and(D2.spell_ok(ps), Bool.and(D1.all_ws(Lex.text(w1)), Bool.and(D1.all_ws(Lex.text(w2)),
            Bool.and(D2.g.ok(g2, D2.GKVal{}), Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gr, D2.GKObj{})))))),
            aw_text(w4, "", a2, {==}), M6.and2(D2.spell_ok(ps), Bool.and(D1.all_ws(Lex.text(w1)),
            Bool.and(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g2, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gr, D2.GKObj{}))))), okp, M6.and2(D1.all_ws(Lex.text(w1)),
            Bool.and(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g2, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gr, D2.GKObj{})))), aw_text(w1, "", a3, {==}),
            M6.and2(D1.all_ws(Lex.text(w2)), Bool.and(D2.g.ok(g2, D2.GKVal{}), Bool.and(D1.all_ws(Lex.text(w3)),
            D2.g.ok(gr, D2.GKObj{}))), aw_text(w2, "", a4, {==}), M6.and2(D2.g.ok(g2, D2.GKVal{}),
            Bool.and(D1.all_ws(Lex.text(w3)), D2.g.ok(gr, D2.GKObj{})), k4, M6.and2(D1.all_ws(Lex.text(w3)),
            D2.g.ok(gr, D2.GKObj{}), aw_text(w3, "", a5, {==}), k5)))))), Equal.trans(List<&2, Char>, M6.fr(fits,
            acc), M6.fr(f1, ',' <> List.append(&2, Char, w, acc)), M6.fr(f5, '}' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc))), e1,
            Equal.trans(List<&2, Char>, M6.fr(f1, ',' <> List.append(&2, Char, w, acc)), M6.fr(f2,
                '"' <> List.reverse.go(&2,
            Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w,
            acc)))), M6.fr(f5, '}' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc))), e2,
            Equal.trans(List<&2, Char>, M6.fr(f2, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))), M6.fr(f3, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), M6.fr(f5, '}' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc))), e3,
            Equal.trans(List<&2, Char>, M6.fr(f3, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))),
            M6.fr(f4, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))))), M6.fr(f5,
            '}' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc))), e4,
            Equal.trans(List<&2, Char>, M6.fr(f4, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w,
            acc))))))), M6.fr(f5, '}' <> List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char,
            w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))))))), M6.fr(f5,
            '}' <> List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc))), e5,
            Equal.cong(List<&2, Char>, List<&2, Char>, zz => M6.fr(f5, '}' <> zz), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc)),
            Equal.sym(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list("," ++ Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++
            Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char,
            String.to_list(Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++
            D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), ',' <> List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w4) ++ "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++
            D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), ',' <> List.append(&2, Char, w, acc)),
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(Lex.text(w4)),
            ',' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w4),
            "\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++
            D2.g.text(gr), ',' <> List.append(&2, Char, w, acc)), Equal.trans(List<&2, Char>, List.reverse.go(&2,
            Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(Lex.text(w4)),
            ',' <> List.append(&2, Char, w, acc))), List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), zz), List.reverse.go(&2, Char, String.to_list(Lex.text(w4)),
            ',' <> List.append(&2, Char, w, acc)), List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)),
            text_rc(w4, "", ',' <> List.append(&2, Char, w, acc))), Equal.trans(List<&2, Char>, List.reverse.go(&2,
            Char,
            String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))),
            List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps) ++ "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++
            Lex.text(w3) ++ D2.g.text(gr)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))),
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++
            D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char,
            w4, ',' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), srev_app(D2.spell(ps),
            "\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))), Equal.trans(List<&2, Char>,
            List.reverse.go(&2, Char,
            String.to_list("\"" ++ Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++
            D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char,
            w4, ',' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)),
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2,
            Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w1) ++ ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)),
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))), List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w1),
            ":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))),
            Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))),
            List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>,
            List<&2, Char>, zz => List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), zz),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w1)), '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))),
            List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))), text_rc(w1, "",
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(":" ++ Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), {==}, Equal.trans(List<&2,
            Char>, List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2) ++ D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w2),
            D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr), ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3, List.reverse.go(&2,
            Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), Equal.cong(List<&2, Char>, List<&2, Char>,
            zz => List.reverse.go(&2, Char, String.to_list(D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), zz),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w2)), ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))), text_rc(w2, "", ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2) ++ Lex.text(w3) ++ D2.g.text(gr)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))), List.reverse.go(&2, Char,
            String.to_list(Lex.text(w3) ++ D2.g.text(gr)), List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w,
            acc))))))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), List.append(&2, Char, w3,
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), srev_app(D2.g.text(g2), Lex.text(w3) ++ D2.g.text(gr),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))),
            Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, String.to_list(Lex.text(w3) ++ D2.g.text(gr)),
            List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2,
            Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc))))))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.reverse.go(&2, Char, String.to_list(Lex.text(w3)), List.reverse.go(&2, Char,
            String.to_list(D2.g.text(g2)), List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1,
            '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4,
            ',' <> List.append(&2, Char, w, acc)))))))), List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)),
            List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char,
            w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc)))))))), srev_app(Lex.text(w3),
            D2.g.text(gr), List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2, Char, w2,
            ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))))), Equal.cong(List<&2, Char>,
            List<&2, Char>, zz => List.reverse.go(&2, Char, String.to_list(D2.g.text(gr)), zz), List.reverse.go(&2,
            Char, String.to_list(Lex.text(w3)), List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w,
            acc))))))), List.append(&2, Char, w3, List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)),
            List.append(&2, Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char,
            String.to_list(D2.spell(ps)), '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w,
            acc))))))), text_rc(w3, "", List.reverse.go(&2, Char, String.to_list(D2.g.text(g2)), List.append(&2,
            Char, w2, ':' <> List.append(&2, Char, w1, '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)),
            '"' <> List.append(&2, Char, w4, ',' <> List.append(&2, Char, w, acc))))))))))))))))))))))))))))))))))))))))

# laws/ParsesExactlyJsonTexts.bend: a text that parses is derived

# is_some sees through own_m
law is_some_own:
  for mb: Maybe<&2, V.Json>
  {D1.is_some(D1.own_m(mb)) == D1.is_some(mb) : Bool}

def is_some_own(mb):
  match mb:
    case None{}:
      {==}
    case Some{_jj}:
      {==}

# a Maybe that holds a value is Some of it
law some_un:
  for +mb: Maybe<&2, V.Json>
  for h: {D1.is_some(mb) == True{} : Bool}
  {mb == Some{M10.unsome(mb)} : Maybe<&2, V.Json>}

def some_un(mb, h):
  match mb:
    case None{}:
      M6.no({None{} == Some{M10.unsome(None{})} : Maybe<&2, V.Json>}, h)
    case Some{_jj}:
      {==}

# a text that parses leaves the character lexer with no error token, once
# whether it does is named
law lnb.at:
  for bb: Bool
  for +txt: String
  for h_s: {D1.short(txt) == True{} : Bool}
  for h_p: {D1.is_some(Ezjson.parse(txt)) == True{} : Bool}
  for e: {M5.has_bad(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))) == bb : Bool}
  {M5.has_bad(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))) == False{} : Bool}

def lnb.at(bb, txt, h_s, h_p, e):
  match bb:
    case True{}:
      M6.no({M5.has_bad(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))) == False{} : Bool},
        Equal.trans(Bool, False{}, D1.is_some(Ezjson.parse(txt)),
        True{}, Equal.sym(Bool, D1.is_some(Ezjson.parse(txt)), False{}, Equal.cong(Maybe<&2, V.Json>, Bool,
          zz => D1.is_some(zz),
        Ezjson.parse(txt), None{}, M5.lex_none(txt, h_s, e))), h_p))
    case False{}:
      e

# a text that parses leaves the character lexer with no error token
law lnb:
  for +txt: String
  for h_s: {D1.short(txt) == True{} : Bool}
  for h_p: {D1.is_some(Ezjson.parse(txt)) == True{} : Bool}
  {M5.has_bad(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))) == False{} : Bool}

def lnb(txt, h_s, h_p):
  lnb.at(M5.has_bad(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))), txt, h_s, h_p, {==})

# a lexer state with no error token at the end, by its mode: lexemes read and
# whitespace, the tokens the lexer ends with being the lexemes'
law lx_fin.m:
  for md: Lex.Mode
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +rc: List<&2, Char>
  for h: jm(md, bf, tk, rc)
  for hb: {M5.has_bad(Lex.finish(Lex.Lex{md, bf, tk})) == False{} : Bool}
  (&its: List<&2, M6.It> -> &rws: List<&2, Char> -> ({rc == List.append(&2, Char, rws, ritems(its)) : List<&2,
    Char>} & ({Lex.finish(Lex.Lex{md, bf, tk}) == List.reverse(&2, Lex.Tok, M13.rtoks(its)) : List<&2,
    Lex.Tok>} & ({M13.itsok(its) == True{} : Bool} & {M13.allws(rws) == True{} : Bool}))))

def lx_fin.m(md, bf, tk, rc, h, hb):
  match md:
    case Lex.Idle{}:
      (+its, (+rws, ((etk, (hok, hws)), erc))) = h
      (its, (rws, (erc, (Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.reverse(&2, Lex.Tok, zz), tk,
        M13.rtoks(its), etk), (hok, hws)))))
    case Lex.Word{}:
      (+its, (+rws, ((etk, (hok, hws)), erc))) = h
      (M6.It{rws, M6.LW{Lex.text(bf)}} <> its, ([], (Equal.trans(List<&2, Char>, rc, List.append(&2, Char, bf,
        List.append(&2, Char, rws, ritems(its))), List.reverse.go(&2, Char, String.to_list(Lex.text(bf)),
        List.append(&2, Char, rws, ritems(its))), erc, Equal.sym(List<&2, Char>, List.reverse.go(&2, Char,
        String.to_list(Lex.text(bf)), List.append(&2, Char, rws, ritems(its))), List.append(&2, Char, bf,
        List.append(&2, Char, rws, ritems(its))), text_rc(bf, "", List.append(&2, Char, rws, ritems(its))))),
        (Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.reverse(&2, Lex.Tok,
          Lex.TWord{Lex.text(bf)} <> zz), tk, M13.rtoks(its), etk), (M6.and2(M13.allws(rws), M13.itsok(its),
        hws, hok), {==})))))
    case Lex.Str{}:
      M6.no((&its: List<&2, M6.It> -> &rws: List<&2, Char> -> ({rc == List.append(&2, Char, rws, ritems(its)) : List<&2,
        Char>} & ({Lex.finish(Lex.Lex{Lex.Str{}, bf, tk}) == List.reverse(&2, Lex.Tok, M13.rtoks(its)) : List<&2,
        Lex.Tok>} & ({M13.itsok(its) == True{} : Bool} & {M13.allws(rws) == True{} : Bool})))), Equal.trans(Bool,
            False{},
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Str{}, bf, tk})), True{}, Equal.sym(Bool,
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Str{}, bf, tk})), False{}, hb), M5.hb_rev(tk, [Lex.TBad{}], {==})))
    case Lex.Esc{}:
      M6.no((&its: List<&2, M6.It> -> &rws: List<&2, Char> -> ({rc == List.append(&2, Char, rws, ritems(its)) : List<&2,
        Char>} & ({Lex.finish(Lex.Lex{Lex.Esc{}, bf, tk}) == List.reverse(&2, Lex.Tok, M13.rtoks(its)) : List<&2,
        Lex.Tok>} & ({M13.itsok(its) == True{} : Bool} & {M13.allws(rws) == True{} : Bool})))), Equal.trans(Bool,
            False{},
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Esc{}, bf, tk})), True{}, Equal.sym(Bool,
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Esc{}, bf, tk})), False{}, hb), M5.hb_rev(tk, [Lex.TBad{}], {==})))
    case Lex.Uni{ul, ua}:
      M6.no((&its: List<&2, M6.It> -> &rws: List<&2, Char> -> ({rc == List.append(&2, Char, rws, ritems(its)) : List<&2,
        Char>} & ({Lex.finish(Lex.Lex{Lex.Uni{ul, ua}, bf, tk}) == List.reverse(&2, Lex.Tok, M13.rtoks(its)) : List<&2,
        Lex.Tok>} & ({M13.itsok(its) == True{} : Bool} & {M13.allws(rws) == True{} : Bool})))), Equal.trans(Bool,
            False{},
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Uni{ul, ua}, bf, tk})), True{}, Equal.sym(Bool,
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Uni{ul, ua}, bf, tk})), False{}, hb), M5.hb_rev(tk, [Lex.TBad{}], {==})))
    case Lex.Hi{uh}:
      M6.no((&its: List<&2, M6.It> -> &rws: List<&2, Char> -> ({rc == List.append(&2, Char, rws, ritems(its)) : List<&2,
        Char>} & ({Lex.finish(Lex.Lex{Lex.Hi{uh}, bf, tk}) == List.reverse(&2, Lex.Tok, M13.rtoks(its)) : List<&2,
        Lex.Tok>} & ({M13.itsok(its) == True{} : Bool} & {M13.allws(rws) == True{} : Bool})))), Equal.trans(Bool,
            False{},
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Hi{uh}, bf, tk})), True{}, Equal.sym(Bool,
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Hi{uh}, bf, tk})), False{}, hb), M5.hb_rev(tk, [Lex.TBad{}], {==})))
    case Lex.HiEsc{uh}:
      M6.no((&its: List<&2, M6.It> -> &rws: List<&2, Char> -> ({rc == List.append(&2, Char, rws, ritems(its)) : List<&2,
        Char>} & ({Lex.finish(Lex.Lex{Lex.HiEsc{uh}, bf, tk}) == List.reverse(&2, Lex.Tok, M13.rtoks(its)) : List<&2,
        Lex.Tok>} & ({M13.itsok(its) == True{} : Bool} & {M13.allws(rws) == True{} : Bool})))), Equal.trans(Bool,
            False{},
        M5.has_bad(Lex.finish(Lex.Lex{Lex.HiEsc{uh}, bf, tk})), True{}, Equal.sym(Bool,
        M5.has_bad(Lex.finish(Lex.Lex{Lex.HiEsc{uh}, bf, tk})), False{}, hb), M5.hb_rev(tk, [Lex.TBad{}], {==})))
    case Lex.Lo{ul, ua, uh}:
      M6.no((&its: List<&2, M6.It> -> &rws: List<&2, Char> -> ({rc == List.append(&2, Char, rws, ritems(its)) : List<&2,
        Char>} & ({Lex.finish(Lex.Lex{Lex.Lo{ul, ua, uh}, bf, tk}) == List.reverse(&2, Lex.Tok,
            M13.rtoks(its)) : List<&2,
        Lex.Tok>} & ({M13.itsok(its) == True{} : Bool} & {M13.allws(rws) == True{} : Bool})))), Equal.trans(Bool,
            False{},
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Lo{ul, ua, uh}, bf, tk})), True{}, Equal.sym(Bool,
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Lo{ul, ua, uh}, bf, tk})), False{}, hb), M5.hb_rev(tk, [Lex.TBad{}], {==})))
    case Lex.Bad{}:
      M6.no((&its: List<&2, M6.It> -> &rws: List<&2, Char> -> ({rc == List.append(&2, Char, rws, ritems(its)) : List<&2,
        Char>} & ({Lex.finish(Lex.Lex{Lex.Bad{}, bf, tk}) == List.reverse(&2, Lex.Tok, M13.rtoks(its)) : List<&2,
        Lex.Tok>} & ({M13.itsok(its) == True{} : Bool} & {M13.allws(rws) == True{} : Bool})))), Equal.trans(Bool,
            False{},
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Bad{}, bf, tk})), True{}, Equal.sym(Bool,
        M5.has_bad(Lex.finish(Lex.Lex{Lex.Bad{}, bf, tk})), False{}, hb), M5.hb_rev(tk, [Lex.TBad{}], {==})))

# a lexer state with no error token at the end
law lx_fin:
  for st: Lex.Lex
  for +rc: List<&2, Char>
  for h: jl(st, rc)
  for hb: {M5.has_bad(Lex.finish(st)) == False{} : Bool}
  (&its: List<&2, M6.It> -> &rws: List<&2, Char> -> ({rc == List.append(&2, Char, rws, ritems(its)) : List<&2,
    Char>} & ({Lex.finish(st) == List.reverse(&2, Lex.Tok, M13.rtoks(its)) : List<&2,
    Lex.Tok>} & ({M13.itsok(its) == True{} : Bool} & {M13.allws(rws) == True{} : Bool}))))

def lx_fin(st, rc, h, hb):
  match st:
    case Lex.Lex{md, +bf, +tk}:
      lx_fin.m(md, bf, tk, rc, h, hb)

# lexemes read, passed on
law use_fin:
  for -gl: Type
  for st: Lex.Lex
  for rc: List<&2, Char>
  for r: (&its: List<&2, M6.It> -> &rws: List<&2, Char> -> ({rc == List.append(&2, Char, rws, ritems(its)) : List<&2,
    Char>} & ({Lex.finish(st) == List.reverse(&2, Lex.Tok, M13.rtoks(its)) : List<&2,
    Lex.Tok>} & ({M13.itsok(its) == True{} : Bool} & {M13.allws(rws) == True{} : Bool}))))
  for kk: @its: List<&2, M6.It> -> @rws: List<&2, Char> -> {rc == List.append(&2, Char, rws, ritems(its)) : List<&2,
    Char>} -> {Lex.finish(st) ==
    List.reverse(&2, Lex.Tok, M13.rtoks(its)) : List<&2,
      Lex.Tok>} -> {M13.itsok(its) == True{} : Bool} -> {M13.allws(rws) == True{} : Bool} -> gl
  gl

def use_fin(_gl, _st, _rc, r, kk):
  (its, (rws, (aa, (bb, (cc, dd))))) = r
  kk(its, rws, aa, bb, cc, dd)

# the derivation read off a text's lexemes and the value its tokens parse to
law derive_from:
  for +its: List<&2, M6.It>
  for +rws: List<&2, Char>
  for +txt: String
  for +jv: V.Json
  for erc: {List.reverse.go(&2, Char, String.to_list(txt), []) == List.append(&2, Char, rws, ritems(its)) : List<&2,
    Char>}
  for efin: {Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []})) == List.reverse(&2, Lex.Tok,
    M13.rtoks(its)) : List<&2, Lex.Tok>}
  for +hok: {M13.itsok(its) == True{} : Bool}
  for +hws: {M13.allws(rws) == True{} : Bool}
  for ptk: {M13.tj_r(jv, V.WVal{}) == M6.dens(Lex.tokens(txt)) : List<&2, Lex.Tok>}
  for la: {M6.dens(Lex.tokens(txt)) == M6.dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [],
    []}))) : List<&2, Lex.Tok>}
  for +wfj: {V.wf.go(jv, V.WVal{}) == True{} : Bool}
  (&wa: String -> &gg: D2.Gv -> &wb: String -> ({txt == wa ++ D2.g.text(gg) ++ wb : String} & {D2.derived(wa, gg,
    wb) == True{} : Bool}))

def derive_from(its, rws, txt, jv, erc, efin, hok, hws, ptk, la, wfj):
  use_bv((&wa: String -> &gg: D2.Gv -> &wb: String -> ({txt == wa ++ D2.g.text(gg) ++
    wb : String} & {D2.derived(wa, gg, wb) == True{} : Bool})), List.reverse.go(&2, M6.It, its, []), [], [], bld(jv,
    V.WVal{}, List.reverse.go(&2, M6.It, its, []), [], [], wfj, Equal.trans(List<&2, Lex.Tok>,
    M6.dens(M13.rtoks(List.reverse.go(&2, M6.It, its, []))), M6.dens(List.reverse.go(&2, Lex.Tok, M13.rtoks(its), [])),
        List.append(&2,
    Lex.Tok, M13.tj_r(jv, V.WVal{}), []), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M6.dens(zz),
    M13.rtoks(List.reverse.go(&2, M6.It, its, [])), List.reverse.go(&2, Lex.Tok, M13.rtoks(its), []), rtoks_rev(its,
        [])),
    Equal.trans(List<&2, Lex.Tok>, M6.dens(List.reverse.go(&2, Lex.Tok, M13.rtoks(its), [])),
    M6.dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))), List.append(&2, Lex.Tok,
        M13.tj_r(jv,
    V.WVal{}), []), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M6.dens(zz), List.reverse.go(&2, Lex.Tok,
    M13.rtoks(its), []), Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []})), Equal.sym(List<&2,
    Lex.Tok>, Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []})), List.reverse(&2, Lex.Tok,
    M13.rtoks(its)), efin)), Equal.trans(List<&2, Lex.Tok>, M6.dens(Lex.finish(Lex.run(String.to_list(txt),
    Lex.Lex{Lex.Idle{}, [], []}))), M6.dens(Lex.tokens(txt)), List.append(&2, Lex.Tok, M13.tj_r(jv, V.WVal{}), []),
    Equal.sym(List<&2, Lex.Tok>, M6.dens(Lex.tokens(txt)), M6.dens(Lex.finish(Lex.run(String.to_list(txt),
    Lex.Lex{Lex.Idle{}, [], []}))), la), Equal.trans(List<&2, Lex.Tok>, M6.dens(Lex.tokens(txt)), M13.tj_r(jv,
        V.WVal{}),
    List.append(&2, Lex.Tok, M13.tj_r(jv, V.WVal{}), []), Equal.sym(List<&2, Lex.Tok>, M13.tj_r(jv, V.WVal{}),
    M6.dens(Lex.tokens(txt)), ptk), Equal.sym(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M13.tj_r(jv, V.WVal{}), []),
    M13.tj_r(jv, V.WVal{}), M4.lapp_nil(M13.tj_r(jv, V.WVal{}))))))), itsok_rev(its, [], hok, {==})),
    +bw => +bg => +br => tb => _ob => ab => kb => eb => (Lex.text(bw), (bg, (Lex.text(rws), (rc_inj(txt,
      Lex.text(bw) ++ D2.g.text(bg) ++ Lex.text(rws), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
      String.to_list(txt), []), List.append(&2, Char, rws, ritems(its)), List.reverse.go(&2, Char,
      String.to_list(Lex.text(bw) ++ D2.g.text(bg) ++ Lex.text(rws)), []), erc, Equal.trans(List<&2, Char>,
      List.append(&2, Char, rws, ritems(its)), List.append(&2, Char, rws, ra(its, [])), List.reverse.go(&2, Char,
      String.to_list(Lex.text(bw) ++ D2.g.text(bg) ++ Lex.text(rws)), []), Equal.cong(List<&2, Char>, List<&2, Char>,
      zz => List.append(&2, Char, rws, zz), ritems(its), ra(its, []), ritems_ra(its)), Equal.trans(List<&2, Char>,
      List.append(&2, Char, rws, ra(its, [])), List.append(&2, Char, rws, M6.fr(List.reverse.go(&2, M6.It, its, []),
          [])),
      List.reverse.go(&2, Char, String.to_list(Lex.text(bw) ++ D2.g.text(bg) ++ Lex.text(rws)), []),
      Equal.cong(List<&2, Char>, List<&2, Char>, zz => List.append(&2, Char, rws, zz), ra(its, []),
      M6.fr(List.reverse.go(&2, M6.It, its, []), []), Equal.sym(List<&2, Char>, M6.fr(List.reverse.go(&2, M6.It, its,
          []), []),
      ra(its, []), fr_rev(its, [], []))), Equal.trans(List<&2, Char>, List.append(&2, Char, rws,
          M6.fr(List.reverse.go(&2,
      M6.It, its, []), [])), List.append(&2, Char, rws, M6.fr(br, List.reverse.go(&2, Char,
          String.to_list(D2.g.text(bg)),
      List.append(&2, Char, bw, [])))), List.reverse.go(&2, Char,
      String.to_list(Lex.text(bw) ++ D2.g.text(bg) ++ Lex.text(rws)), []), Equal.cong(List<&2, Char>, List<&2, Char>,
      zz => List.append(&2, Char, rws, zz), M6.fr(List.reverse.go(&2, M6.It, its, []), []), M6.fr(br,
          List.reverse.go(&2, Char,
      String.to_list(D2.g.text(bg)), List.append(&2, Char, bw, []))), eb), Equal.trans(List<&2, Char>,
      List.append(&2, Char, rws, M6.fr(br, List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2,
      Char, bw, [])))), List.append(&2, Char, rws, List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)),
      List.append(&2, Char, bw, []))), List.reverse.go(&2, Char,
      String.to_list(Lex.text(bw) ++ D2.g.text(bg) ++ Lex.text(rws)), []), Equal.cong(List<&2, M6.It>, List<&2, Char>,
      zz => List.append(&2, Char, rws, M6.fr(zz, List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)),
      List.append(&2, Char, bw, [])))), br, [], its_nil(br, tb)), Equal.sym(List<&2, Char>, List.reverse.go(&2, Char,
      String.to_list(Lex.text(bw) ++ D2.g.text(bg) ++ Lex.text(rws)), []), List.append(&2, Char, rws,
      List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2, Char, bw, []))), Equal.trans(List<&2,
      Char>, List.reverse.go(&2, Char, String.to_list(Lex.text(bw) ++ D2.g.text(bg) ++ Lex.text(rws)), []),
      List.reverse.go(&2, Char, String.to_list(D2.g.text(bg) ++ Lex.text(rws)), List.reverse.go(&2, Char,
      String.to_list(Lex.text(bw)), [])), List.append(&2, Char, rws, List.reverse.go(&2, Char,
      String.to_list(D2.g.text(bg)), List.append(&2, Char, bw, []))), srev_app(Lex.text(bw),
      D2.g.text(bg) ++ Lex.text(rws), []), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
      String.to_list(D2.g.text(bg) ++ Lex.text(rws)), List.reverse.go(&2, Char, String.to_list(Lex.text(bw)), [])),
      List.reverse.go(&2, Char, String.to_list(D2.g.text(bg) ++ Lex.text(rws)), List.append(&2, Char, bw, [])),
      List.append(&2, Char, rws, List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2, Char, bw,
      []))), Equal.cong(List<&2, Char>, List<&2, Char>, zz => List.reverse.go(&2, Char,
      String.to_list(D2.g.text(bg) ++ Lex.text(rws)), zz), List.reverse.go(&2, Char, String.to_list(Lex.text(bw)),
      []), List.append(&2, Char, bw, []), text_rc(bw, "", [])), Equal.trans(List<&2, Char>, List.reverse.go(&2, Char,
      String.to_list(D2.g.text(bg) ++ Lex.text(rws)), List.append(&2, Char, bw, [])), List.reverse.go(&2, Char,
      String.to_list(Lex.text(rws)), List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2, Char,
      bw, []))), List.append(&2, Char, rws, List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2,
      Char, bw, []))), srev_app(D2.g.text(bg), Lex.text(rws), List.append(&2, Char, bw, [])), text_rc(rws, "",
      List.reverse.go(&2, Char, String.to_list(D2.g.text(bg)), List.append(&2, Char, bw, []))))))))))))),
      M6.and2(D1.all_ws(Lex.text(bw)), Bool.and(D2.g.ok(bg, D2.GKVal{}), D1.all_ws(Lex.text(rws))), aw_text(bw,
      "", ab, {==}), M6.and2(D2.g.ok(bg, D2.GKVal{}), D1.all_ws(Lex.text(rws)), kb, aw_text(rws, "", hws,
      {==}))))))))

def L3.text_derives(txt, h_s, h_p):
  use_fin((&wa: String -> &gg: D2.Gv -> &wb: String -> ({txt == wa ++ D2.g.text(gg) ++
    wb : String} & {D2.derived(wa, gg, wb) == True{} : Bool})), Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [],
    []}), List.reverse.go(&2, Char, String.to_list(txt), []), lx_fin(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{},
    [], []}), List.reverse.go(&2, Char, String.to_list(txt), []), jrun(String.to_list(txt), Lex.Lex{Lex.Idle{}, [],
    []}, [], ([], ([], (({==}, ({==},
    {==})), {==})))), lnb(txt, h_s, h_p)), +its => +rws => erc => efin => hok => hws => derive_from(its, rws, txt,
      M10.unsome(Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}))), erc,
    efin, hok, hws, parse_toks(Lex.tokens(txt), M10.unsome(Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)),
        Parse.P{False{},
      None{}, Nil{}}))), some_un(Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})),
      Equal.trans(Bool, D1.is_some(Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}))),
      D1.is_some(D1.own_m(Ezjson.parse(txt))), True{}, Equal.cong(Maybe<&2, V.Json>, Bool, zz => D1.is_some(zz),
      Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})), D1.own_m(Ezjson.parse(txt)),
      Equal.sym(Maybe<&2, V.Json>, D1.own_m(Parse.finish(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{},
      Nil{}}))), Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})),
          Equal.trans(Maybe<&2,
      V.Json>, D1.own_m(Parse.finish(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}))),
      Parse.finish(M9.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}))),
      Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})),
      M9.fin_own(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})), Equal.cong(Parse.P, Maybe<&2, V.Json>,
      zz => Parse.finish(zz), M9.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})),
      Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}), M9.run_own(Lex.tokens(txt), Parse.P{False{},
      None{}, Nil{}}))))), Equal.trans(Bool, D1.is_some(D1.own_m(Ezjson.parse(txt))),
      D1.is_some(Ezjson.parse(txt)), True{}, is_some_own(Ezjson.parse(txt)), h_p)))), M2.lexers_agree(txt, h_s),
      Equal.trans(Bool, V.wf(M10.unsome(Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{},
          Nil{}})))),
      L1.wf_m(Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}))), True{},
      Equal.sym(Bool, L1.wf_m(Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}))),
      V.wf(M10.unsome(Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})))),
      Equal.cong(Maybe<&2, V.Json>, Bool, zz => L1.wf_m(zz), Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)),
      Parse.P{False{}, None{}, Nil{}})), Some{M10.unsome(Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)),
          Parse.P{False{},
      None{}, Nil{}})))}, some_un(Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})),
      Equal.trans(Bool, D1.is_some(Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}))),
      D1.is_some(D1.own_m(Ezjson.parse(txt))), True{}, Equal.cong(Maybe<&2, V.Json>, Bool, zz => D1.is_some(zz),
      Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})), D1.own_m(Ezjson.parse(txt)),
      Equal.sym(Maybe<&2, V.Json>, D1.own_m(Parse.finish(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{},
      Nil{}}))), Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})),
          Equal.trans(Maybe<&2,
      V.Json>, D1.own_m(Parse.finish(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}))),
      Parse.finish(M9.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}))),
      Parse.finish(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})),
      M9.fin_own(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})), Equal.cong(Parse.P, Maybe<&2, V.Json>,
      zz => Parse.finish(zz), M9.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})),
      Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}), M9.run_own(Lex.tokens(txt), Parse.P{False{},
      None{}, Nil{}}))))), Equal.trans(Bool, D1.is_some(D1.own_m(Ezjson.parse(txt))),
      D1.is_some(Ezjson.parse(txt)), True{}, is_some_own(Ezjson.parse(txt)), h_p))))),
      M11.fin_inv(Parse.run(M6.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}),
          M11.run_inv(M6.dens(Lex.tokens(txt)),
      Parse.P{False{}, None{}, Nil{}}, (Unit{}, Unit{}))))))

# is_cp 34 is classify's quotation mark
law cq.at:
  for +uu: U32
  for cls: Lex.Class
  for e: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  {U32.is_eq(uu, 34) == M2.is_quote(cls) : Bool}

def cq.at(uu, cls, e):
  match cls:
    case Lex.CPunct{+tk}:
      M5.nq(U32.is_eq(uu, 34), uu, Lex.CPunct{tk}, {==}, e, {==})
    case Lex.CQuote{}:
      Equal.cong(U32, Bool, zz => U32.is_eq(zz, 34), uu, 34, M2.cls_quote(Chr{uu}, e))
    case Lex.CBack{}:
      M5.nq(U32.is_eq(uu, 34), uu, Lex.CBack{}, {==}, e, {==})
    case Lex.CSpace{}:
      M5.nq(U32.is_eq(uu, 34), uu, Lex.CSpace{}, {==}, e, {==})
    case Lex.COther{}:
      M5.nq(U32.is_eq(uu, 34), uu, Lex.COther{}, {==}, e, {==})

law cq:
  for +ch: Char
  {D1.is_cp(ch, 34) == M2.is_quote(Lex.classify(ch)) : Bool}

def cq(ch):
  match ch:
    case Chr{+uu}:
      cq.at(uu, Lex.classify(Chr{uu}), {==})
