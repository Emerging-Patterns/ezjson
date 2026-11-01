# proofs of laws/PrintIsCompactAndStable.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lex.bend as Lex
import ../src/print.bend as Print
import ../laws/BuiltValuesWellFormed.bend as L1
import ../laws/NumOkIsNumberRule.bend as L2
import ../laws/PrintIsCompactAndStable.bend as Laws
import ../laws/PrintRoundTrips.bend as L3
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/LexemeOrder.bend as M2
import ./lemmas/NumberCharsAreWordChars.bend as M3
import ./lemmas/NumberDigits.bend as M4
import ./lemmas/ParserStateCloses.bend as M5
import ./lemmas/PrintFix.bend as M6
import ./lemmas/WellFormedCells.bend as M7
import ./lemmas/WordLexing.bend as M8

# laws/PrintIsCompactAndStable.bend, the second half: printing does not see spans or the fix

# esc_fix, with the scalar test named
law esc_fix.go:
  for bb: Bool
  for +uu: U32
  for eb: {D1.non_scalar(uu) == bb : Bool}
  {Print.escape.char(Bool.pick(Char, bb, Char.from_u32(65533), Chr{uu})) == Print.escape.char(Chr{uu}) : String}

def esc_fix.go(bb, uu, eb):
  match bb:
    case True{}:
      es = Equal.sym(Bool, D1.non_scalar(uu), True{}, eb)
      %es : {Print.escape.char(Char.from_u32(65533)) == Print.escape.scalar(uu, Chr{uu}, Bool.not(_)) : String}
      {==}
    case False{}:
      {==}

# a character and its fix print the same
law esc_fix:
  for +ch: Char
  {Print.escape.char(D1.fix_char(ch)) == Print.escape.char(ch) : String}

def esc_fix(ch):
  match ch:
    case Chr{+uu}:
      esc_fix.go(D1.non_scalar(uu), uu, {==})

# a string and its fix print the same
law quote_fix:
  for +txt: String
  {Print.escape(String.to_list(D1.fix_str(txt))) == Print.escape(String.to_list(txt)) : String}

def quote_fix(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      e1 = esc_fix(hd)
      e2 = quote_fix(tl)
      %e1 : {Print.escape.char(D1.fix_char(hd)) ++ Print.escape(String.to_list(D1.fix_str(tl))) ==
        _ ++ Print.escape(String.to_list(tl)) : String}
      %e2 : {Print.escape.char(D1.fix_char(hd)) ++ Print.escape(String.to_list(D1.fix_str(tl))) ==
        Print.escape.char(D1.fix_char(hd)) ++ _ : String}
      {==}

# print_fix for an array cell, by what follows it
law pf_cons:
  for tl: V.Json
  for +hd: V.Json
  for +eh: {Print.print(D1.fixv(hd)) == Print.print(hd) : String}
  for +et: {Print.print(D1.fixv(tl)) == Print.print(tl) : String}
  {Print.print(D1.fixv(V.JCons{hd, tl})) == Print.print(V.JCons{hd, tl}) : String}

def pf_cons(tl, hd, eh, et):
  match tl:
    case V.JNil{}:
      eh
    case V.JNull{}:
      %eh : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JNull{})) == _ ++ "," ++
        Print.print(V.JNull{}) : String}
      %et : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JNull{})) == Print.print(D1.fixv(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JBool{+t1}:
      %eh : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JBool{t1})) == _ ++ "," ++
        Print.print(V.JBool{t1}) : String}
      %et : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JBool{t1})) == Print.print(D1.fixv(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JNum{+t1}:
      %eh : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JNum{t1})) == _ ++ "," ++
        Print.print(V.JNum{t1}) : String}
      %et : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JNum{t1})) == Print.print(D1.fixv(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JStr{+t1}:
      %eh : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JStr{t1})) == _ ++ "," ++
        Print.print(V.JStr{t1}) : String}
      %et : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JStr{t1})) == Print.print(D1.fixv(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JArr{+t1}:
      %eh : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JArr{t1})) == _ ++ "," ++
        Print.print(V.JArr{t1}) : String}
      %et : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JArr{t1})) == Print.print(D1.fixv(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JObj{+t1}:
      %eh : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JObj{t1})) == _ ++ "," ++
        Print.print(V.JObj{t1}) : String}
      %et : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JObj{t1})) == Print.print(D1.fixv(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JCons{+t1, +t2}:
      %eh : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JCons{t1,
        t2})) == _ ++ "," ++ Print.print(V.JCons{t1, t2}) : String}
      %et : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JCons{t1,
        t2})) == Print.print(D1.fixv(hd)) ++ "," ++ _ : String}
      {==}
    case V.JPair{+t1, +t2, +t3}:
      %eh : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JPair{t1, t2,
        t3})) == _ ++ "," ++ Print.print(V.JPair{t1, t2, t3}) : String}
      %et : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JPair{t1, t2,
        t3})) == Print.print(D1.fixv(hd)) ++ "," ++ _ : String}
      {==}
    case V.JSpan{+t1, +t2}:
      %eh : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JSpan{t1,
        t2})) == _ ++ "," ++ Print.print(V.JSpan{t1, t2}) : String}
      %et : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JSpan{t1,
        t2})) == Print.print(D1.fixv(hd)) ++ "," ++ _ : String}
      {==}
    case V.JBind{+t1, +t2, +t3, +t4}:
      %eh : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JBind{t1, t2, t3,
        t4})) == _ ++ "," ++ Print.print(V.JBind{t1, t2, t3, t4}) : String}
      %et : {Print.print(D1.fixv(hd)) ++ "," ++ Print.print(D1.fixv(V.JBind{t1, t2, t3,
        t4})) == Print.print(D1.fixv(hd)) ++ "," ++ _ : String}
      {==}

# print_fix for an object cell, by what follows it
law pf_pair:
  for rr: V.Json
  for +kk: String
  for +vv: V.Json
  for +ek: {Print.quote(D1.fix_str(kk)) == Print.quote(kk) : String}
  for +ev: {Print.print(D1.fixv(vv)) == Print.print(vv) : String}
  for +er: {Print.print(D1.fixv(rr)) == Print.print(rr) : String}
  {Print.print(D1.fixv(V.JPair{kk, vv, rr})) == Print.print(V.JPair{kk, vv, rr}) : String}

def pf_pair(rr, kk, vv, ek, ev, er):
  match rr:
    case V.JNil{}:
      %ek : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) == _ ++ ":" ++ Print.print(vv) : String}
      %ev : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) == Print.quote(D1.fix_str(kk)) ++
        ":" ++ _ : String}
      {==}
    case V.JNull{}:
      %ek : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JNull{})) ==
        _ ++ ":" ++ Print.print(vv) ++ "," ++ Print.print(V.JNull{}) : String}
      %ev : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JNull{})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ _ ++ "," ++ Print.print(V.JNull{}) : String}
      %er : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JNull{})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JBool{+t1}:
      %ek : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JBool{t1})) ==
        _ ++ ":" ++ Print.print(vv) ++ "," ++ Print.print(V.JBool{t1}) : String}
      %ev : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JBool{t1})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ _ ++ "," ++ Print.print(V.JBool{t1}) : String}
      %er : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JBool{t1})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JNum{+t1}:
      %ek : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JNum{t1})) ==
        _ ++ ":" ++ Print.print(vv) ++ "," ++ Print.print(V.JNum{t1}) : String}
      %ev : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JNum{t1})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ _ ++ "," ++ Print.print(V.JNum{t1}) : String}
      %er : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JNum{t1})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JStr{+t1}:
      %ek : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JStr{t1})) ==
        _ ++ ":" ++ Print.print(vv) ++ "," ++ Print.print(V.JStr{t1}) : String}
      %ev : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JStr{t1})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ _ ++ "," ++ Print.print(V.JStr{t1}) : String}
      %er : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JStr{t1})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JArr{+t1}:
      %ek : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JArr{t1})) ==
        _ ++ ":" ++ Print.print(vv) ++ "," ++ Print.print(V.JArr{t1}) : String}
      %ev : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JArr{t1})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ _ ++ "," ++ Print.print(V.JArr{t1}) : String}
      %er : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JArr{t1})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JObj{+t1}:
      %ek : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JObj{t1})) ==
        _ ++ ":" ++ Print.print(vv) ++ "," ++ Print.print(V.JObj{t1}) : String}
      %ev : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JObj{t1})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ _ ++ "," ++ Print.print(V.JObj{t1}) : String}
      %er : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JObj{t1})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JCons{+t1, +t2}:
      %ek : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JCons{t1, t2})) ==
        _ ++ ":" ++ Print.print(vv) ++ "," ++ Print.print(V.JCons{t1, t2}) : String}
      %ev : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JCons{t1, t2})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ _ ++ "," ++ Print.print(V.JCons{t1, t2}) : String}
      %er : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JCons{t1, t2})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JPair{+t1, +t2, +t3}:
      %ek : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JPair{t1, t2, t3})) ==
        _ ++ ":" ++ Print.print(vv) ++ "," ++ Print.print(V.JPair{t1, t2, t3}) : String}
      %ev : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JPair{t1, t2, t3})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ _ ++ "," ++ Print.print(V.JPair{t1, t2, t3}) : String}
      %er : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JPair{t1, t2, t3})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JSpan{+t1, +t2}:
      %ek : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JSpan{t1, t2})) ==
        _ ++ ":" ++ Print.print(vv) ++ "," ++ Print.print(V.JSpan{t1, t2}) : String}
      %ev : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JSpan{t1, t2})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ _ ++ "," ++ Print.print(V.JSpan{t1, t2}) : String}
      %er : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JSpan{t1, t2})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JBind{+t1, +t2, +t3, +t4}:
      %ek : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JBind{t1, t2, t3, t4})) ==
        _ ++ ":" ++ Print.print(vv) ++ "," ++ Print.print(V.JBind{t1, t2, t3, t4}) : String}
      %ev : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JBind{t1, t2, t3, t4})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ _ ++ "," ++ Print.print(V.JBind{t1, t2, t3, t4}) : String}
      %er : {Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++
        Print.print(D1.fixv(V.JBind{t1, t2, t3, t4})) ==
        Print.quote(D1.fix_str(kk)) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}

# print_fix for an object cell with a span key, by what follows it
law pf_bind:
  for rr: V.Json
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for +ev: {Print.print(D1.fixv(vv)) == Print.print(vv) : String}
  for +er: {Print.print(D1.fixv(rr)) == Print.print(rr) : String}
  {Print.print(D1.fixv(V.JBind{src, nn, vv, rr})) == Print.print(V.JBind{src, nn, vv, rr}) : String}

def pf_bind(rr, src, nn, vv, ev, er):
  match rr:
    case V.JNil{}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) == Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ _ : String}
      {==}
    case V.JNull{}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JNull{})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JNull{}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JNull{})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JBool{+t1}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JBool{t1})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JBool{t1}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JBool{t1})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JNum{+t1}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JNum{t1})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JNum{t1}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JNum{t1})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JStr{+t1}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JStr{t1})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JStr{t1}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JStr{t1})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JArr{+t1}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JArr{t1})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JArr{t1}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JArr{t1})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JObj{+t1}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JObj{t1})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JObj{t1}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JObj{t1})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JCons{+t1, +t2}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JCons{t1, t2})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JCons{t1, t2}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JCons{t1, t2})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JPair{+t1, +t2, +t3}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JPair{t1, t2, t3})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JPair{t1, t2,
          t3}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JPair{t1, t2, t3})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JSpan{+t1, +t2}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JSpan{t1, t2})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JSpan{t1, t2}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JSpan{t1, t2})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}
    case V.JBind{+t1, +t2, +t3, +t4}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JBind{t1, t2, t3,
        t4})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JBind{t1, t2, t3,
          t4}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ Print.print(D1.fixv(V.JBind{t1, t2, t3,
        t4})) ==
        Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.fixv(vv)) ++ "," ++ _ : String}
      {==}

# a value and its fix print the same
law print_fix:
  for +val: V.Json
  {Print.print(D1.fixv(val)) == Print.print(val) : String}

def print_fix(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      e1 = quote_fix(x1)
      %e1 : {"\"" ++ Print.escape(String.to_list(D1.fix_str(x1))) ++ "\"" == "\"" ++ _ ++ "\"" : String}
      {==}
    case V.JArr{+x1}:
      e1 = print_fix(x1)
      %e1 : {"[" ++ Print.print(D1.fixv(x1)) ++ "]" == "[" ++ _ ++ "]" : String}
      {==}
    case V.JObj{+x1}:
      e1 = print_fix(x1)
      %e1 : {"{" ++ Print.print(D1.fixv(x1)) ++ "}" == "{" ++ _ ++ "}" : String}
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      pf_cons(x2, x1, print_fix(x1), print_fix(x2))
    case V.JPair{+x1, +x2, +x3}:
      pf_pair(x3, x1, x2, Equal.cong(String, String, zz => "\"" ++ zz ++ "\"",
        Print.escape(String.to_list(D1.fix_str(x1))), Print.escape(String.to_list(x1)), quote_fix(x1)), print_fix(x2),
        print_fix(x3))
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      pf_bind(x4, x1, x2, x3, print_fix(x3), print_fix(x4))

# print_own for an array cell, by what follows it
law po_cons:
  for tl: V.Json
  for +hd: V.Json
  for +eh: {Print.print(D1.own(hd)) == Print.print(hd) : String}
  for +et: {Print.print(D1.own(tl)) == Print.print(tl) : String}
  {Print.print(D1.own(V.JCons{hd, tl})) == Print.print(V.JCons{hd, tl}) : String}

def po_cons(tl, hd, eh, et):
  match tl:
    case V.JNil{}:
      eh
    case V.JNull{}:
      %eh : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JNull{})) == _ ++ "," ++
        Print.print(V.JNull{}) : String}
      %et : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JNull{})) == Print.print(D1.own(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JBool{+t1}:
      %eh : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JBool{t1})) == _ ++ "," ++
        Print.print(V.JBool{t1}) : String}
      %et : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JBool{t1})) == Print.print(D1.own(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JNum{+t1}:
      %eh : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JNum{t1})) == _ ++ "," ++
        Print.print(V.JNum{t1}) : String}
      %et : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JNum{t1})) == Print.print(D1.own(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JStr{+t1}:
      %eh : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JStr{t1})) == _ ++ "," ++
        Print.print(V.JStr{t1}) : String}
      %et : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JStr{t1})) == Print.print(D1.own(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JArr{+t1}:
      %eh : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JArr{t1})) == _ ++ "," ++
        Print.print(V.JArr{t1}) : String}
      %et : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JArr{t1})) == Print.print(D1.own(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JObj{+t1}:
      %eh : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JObj{t1})) == _ ++ "," ++
        Print.print(V.JObj{t1}) : String}
      %et : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JObj{t1})) == Print.print(D1.own(hd)) ++
        "," ++ _ : String}
      {==}
    case V.JCons{+t1, +t2}:
      %eh : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JCons{t1,
        t2})) == _ ++ "," ++ Print.print(V.JCons{t1, t2}) : String}
      %et : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JCons{t1,
        t2})) == Print.print(D1.own(hd)) ++ "," ++ _ : String}
      {==}
    case V.JPair{+t1, +t2, +t3}:
      %eh : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JPair{t1, t2,
        t3})) == _ ++ "," ++ Print.print(V.JPair{t1, t2, t3}) : String}
      %et : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JPair{t1, t2,
        t3})) == Print.print(D1.own(hd)) ++ "," ++ _ : String}
      {==}
    case V.JSpan{+t1, +t2}:
      %eh : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JSpan{t1,
        t2})) == _ ++ "," ++ Print.print(V.JSpan{t1, t2}) : String}
      %et : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JSpan{t1,
        t2})) == Print.print(D1.own(hd)) ++ "," ++ _ : String}
      {==}
    case V.JBind{+t1, +t2, +t3, +t4}:
      %eh : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JBind{t1, t2, t3,
        t4})) == _ ++ "," ++ Print.print(V.JBind{t1, t2, t3, t4}) : String}
      %et : {Print.print(D1.own(hd)) ++ "," ++ Print.print(D1.own(V.JBind{t1, t2, t3,
        t4})) == Print.print(D1.own(hd)) ++ "," ++ _ : String}
      {==}

# print_own for an object cell, by what follows it
law po_pair:
  for rr: V.Json
  for +kk: String
  for +vv: V.Json
  for +ev: {Print.print(D1.own(vv)) == Print.print(vv) : String}
  for +er: {Print.print(D1.own(rr)) == Print.print(rr) : String}
  {Print.print(D1.own(V.JPair{kk, vv, rr})) == Print.print(V.JPair{kk, vv, rr}) : String}

def po_pair(rr, kk, vv, ev, er):
  match rr:
    case V.JNil{}:
      %ev : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) == Print.quote(kk) ++ ":" ++ _ : String}
      {==}
    case V.JNull{}:
      %ev : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JNull{})) ==
        Print.quote(kk) ++ ":" ++ _ ++ "," ++ Print.print(V.JNull{}) : String}
      %er : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JNull{})) ==
        Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JBool{+t1}:
      %ev : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JBool{t1})) ==
        Print.quote(kk) ++ ":" ++ _ ++ "," ++ Print.print(V.JBool{t1}) : String}
      %er : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JBool{t1})) ==
        Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JNum{+t1}:
      %ev : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JNum{t1})) ==
        Print.quote(kk) ++ ":" ++ _ ++ "," ++ Print.print(V.JNum{t1}) : String}
      %er : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JNum{t1})) ==
        Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JStr{+t1}:
      %ev : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JStr{t1})) ==
        Print.quote(kk) ++ ":" ++ _ ++ "," ++ Print.print(V.JStr{t1}) : String}
      %er : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JStr{t1})) ==
        Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JArr{+t1}:
      %ev : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JArr{t1})) ==
        Print.quote(kk) ++ ":" ++ _ ++ "," ++ Print.print(V.JArr{t1}) : String}
      %er : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JArr{t1})) ==
        Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JObj{+t1}:
      %ev : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JObj{t1})) ==
        Print.quote(kk) ++ ":" ++ _ ++ "," ++ Print.print(V.JObj{t1}) : String}
      %er : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JObj{t1})) ==
        Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JCons{+t1, +t2}:
      %ev : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JCons{t1,
        t2})) == Print.quote(kk) ++ ":" ++ _ ++ "," ++ Print.print(V.JCons{t1, t2}) : String}
      %er : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JCons{t1,
        t2})) == Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JPair{+t1, +t2, +t3}:
      %ev : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JPair{t1, t2,
        t3})) == Print.quote(kk) ++ ":" ++ _ ++ "," ++ Print.print(V.JPair{t1, t2, t3}) : String}
      %er : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JPair{t1, t2,
        t3})) == Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JSpan{+t1, +t2}:
      %ev : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JSpan{t1,
        t2})) == Print.quote(kk) ++ ":" ++ _ ++ "," ++ Print.print(V.JSpan{t1, t2}) : String}
      %er : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JSpan{t1,
        t2})) == Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JBind{+t1, +t2, +t3, +t4}:
      %ev : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JBind{t1, t2, t3,
        t4})) == Print.quote(kk) ++ ":" ++ _ ++ "," ++ Print.print(V.JBind{t1, t2, t3, t4}) : String}
      %er : {Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JBind{t1, t2, t3,
        t4})) == Print.quote(kk) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}

# print_own for an object cell, by what follows it
law po_bind:
  for rr: V.Json
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for +ev: {Print.print(D1.own(vv)) == Print.print(vv) : String}
  for +er: {Print.print(D1.own(rr)) == Print.print(rr) : String}
  {Print.print(D1.own(V.JBind{src, nn, vv, rr})) == Print.print(V.JBind{src, nn, vv, rr}) : String}

def po_bind(rr, src, nn, vv, ev, er):
  match rr:
    case V.JNil{}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) == Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ _ : String}
      {==}
    case V.JNull{}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JNull{})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JNull{}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JNull{})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JBool{+t1}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JBool{t1})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JBool{t1}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JBool{t1})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JNum{+t1}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JNum{t1})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JNum{t1}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JNum{t1})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JStr{+t1}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JStr{t1})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JStr{t1}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JStr{t1})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JArr{+t1}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JArr{t1})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JArr{t1}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JArr{t1})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JObj{+t1}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JObj{t1})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JObj{t1}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JObj{t1})) ==
          Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JCons{+t1, +t2}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JCons{t1,
        t2})) == Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JCons{t1,
        t2}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JCons{t1,
        t2})) == Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JPair{+t1, +t2, +t3}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JPair{t1, t2,
        t3})) == Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JPair{t1, t2,
        t3}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JPair{t1, t2,
        t3})) == Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JSpan{+t1, +t2}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JSpan{t1,
        t2})) == Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JSpan{t1,
        t2}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JSpan{t1,
        t2})) == Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}
    case V.JBind{+t1, +t2, +t3, +t4}:
      %ev : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JBind{t1, t2, t3,
        t4})) == Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ _ ++ "," ++ Print.print(V.JBind{t1, t2,
        t3, t4}) : String}
      %er : {Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ Print.print(D1.own(V.JBind{t1, t2, t3,
        t4})) == Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ ":" ++ Print.print(D1.own(vv)) ++ "," ++ _ :
        String}
      {==}

# a value and its owned form print the same
law print_own:
  for +val: V.Json
  {Print.print(D1.own(val)) == Print.print(val) : String}

def print_own(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      e1 = print_own(x1)
      %e1 : {"[" ++ Print.print(D1.own(x1)) ++ "]" == "[" ++ _ ++ "]" : String}
      {==}
    case V.JObj{+x1}:
      e1 = print_own(x1)
      %e1 : {"{" ++ Print.print(D1.own(x1)) ++ "}" == "{" ++ _ ++ "}" : String}
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      po_cons(x2, x1, print_own(x1), print_own(x2))
    case V.JPair{+x1, +x2, +x3}:
      po_pair(x3, x1, x2, print_own(x2), print_own(x3))
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      po_bind(x4, x1, x2, x3, print_own(x3), print_own(x4))

# a parse result and its owned form print the same
law print_m_own:
  for mb: Maybe<&2, V.Json>
  {Laws.print_m(D1.own_m(mb)) == Laws.print_m(mb) : Maybe<&2, String>}

def print_m_own(mb):
  match mb:
    case None{}:
      {==}
    case Some{+jj}:
      Equal.cong(String, Maybe<&2, String>, zz => Some{zz}, Print.print(D1.own(jj)), Print.print(jj), print_own(jj))

# laws/PrintIsCompactAndStable.bend, the second half
def Laws.print_stable(txt, jj, e_p, h_s):
  +mm = Ezjson.parse(Ezjson.print(jj))
  hw = Equal.trans(Bool, V.wf(jj), L1.wf_m(Ezjson.parse(txt)), True{},
    Equal.sym(Bool, L1.wf_m(Ezjson.parse(txt)), V.wf(jj), Equal.cong(Maybe<&2, V.Json>, Bool, zz => L1.wf_m(zz),
      Ezjson.parse(txt),
      Some{jj}, e_p)), L1.parse_wf(txt))
  Equal.trans(Maybe<&2, String>, Laws.print_m(mm), Laws.print_m(D1.own_m(mm)), Some{Print.print(jj)},
    Equal.sym(Maybe<&2, String>, Laws.print_m(D1.own_m(mm)), Laws.print_m(mm), print_m_own(mm)),
    Equal.trans(Maybe<&2, String>, Laws.print_m(D1.own_m(mm)), Laws.print_m(Some{D1.fixv(D1.own(jj))}),
      Some{Print.print(jj)},
      Equal.cong(Maybe<&2, V.Json>, Maybe<&2, String>, zz => Laws.print_m(zz), D1.own_m(mm),
        Some{D1.fixv(D1.own(jj))},
        L3.print_parse(jj, hw, h_s)),
      Equal.trans(Maybe<&2, String>, Some{Print.print(D1.fixv(D1.own(jj)))}, Some{Print.print(D1.own(jj))},
        Some{Print.print(jj)},
        Equal.cong(String, Maybe<&2, String>, zz => Some{zz}, Print.print(D1.fixv(D1.own(jj))),
          Print.print(D1.own(jj)),
          print_fix(D1.own(jj))),
        Equal.cong(String, Maybe<&2, String>, zz => Some{zz}, Print.print(D1.own(jj)), Print.print(jj),
          print_own(jj)))))

# laws/PrintIsCompactAndStable.bend, the first half: print writes whitespace only inside strings

# the scan on two strings is the scan on the first, then the second
law tx_app:
  for +aa: String
  for +bb: String
  for st: Laws.Tx
  {Laws.tx.run(String.to_list(aa ++ bb), st) == Laws.tx.run(String.to_list(bb), Laws.tx.run(String.to_list(aa),
    st)) : Laws.Tx}

def tx_app(aa, bb, st):
  match aa:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      tx_app(tl, bb, Laws.tx.step(st, hd))

# the scan on two strings, where the first leads to a known state
law tseq:
  for +aa: String
  for +bb: String
  for +st: Laws.Tx
  for +mid: Laws.Tx
  for e1: {Laws.tx.run(String.to_list(aa), st) == mid : Laws.Tx}
  {Laws.tx.run(String.to_list(aa ++ bb), st) == Laws.tx.run(String.to_list(bb), mid) : Laws.Tx}

def tseq(aa, bb, st, mid, e1):
  Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(aa ++ bb), st), Laws.tx.run(String.to_list(bb),
    Laws.tx.run(String.to_list(aa), st)), Laws.tx.run(String.to_list(bb), mid), tx_app(aa, bb, st),
    Equal.cong(Laws.Tx, Laws.Tx, zz => Laws.tx.run(String.to_list(bb), zz), Laws.tx.run(String.to_list(aa), st), mid,
      e1))

# tx_other, with the code point's tests known
law tx_other.go:
  for +uu: U32
  for e34: {U32.is_eq(uu, 34) == False{} : Bool}
  for e32: {U32.is_eq(uu, 32) == False{} : Bool}
  for e9: {U32.is_eq(uu, 9) == False{} : Bool}
  for e10: {U32.is_eq(uu, 10) == False{} : Bool}
  for e13: {U32.is_eq(uu, 13) == False{} : Bool}
  {Laws.tx.step(Laws.TxOut{}, Chr{uu}) == Laws.TxOut{} : Laws.Tx}

def tx_other.go(uu, e34, e32, e9, e10, e13):
  s34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, e34)
  s32 = Equal.sym(Bool, U32.is_eq(uu, 32), False{}, e32)
  s9 = Equal.sym(Bool, U32.is_eq(uu, 9), False{}, e9)
  s10 = Equal.sym(Bool, U32.is_eq(uu, 10), False{}, e10)
  s13 = Equal.sym(Bool, U32.is_eq(uu, 13), False{}, e13)
  %s34 : {Bool.pick(Laws.Tx, _, Laws.TxIn{}, Bool.pick(Laws.Tx, Bool.or(U32.is_eq(uu, 32), Bool.or(U32.is_eq(uu, 9),
    Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)))), Laws.TxWs{}, Laws.TxOut{})) == Laws.TxOut{} : Laws.Tx}
  %s32 : {Bool.pick(Laws.Tx, Bool.or(_, Bool.or(U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)))),
    Laws.TxWs{}, Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}
  %s9 : {Bool.pick(Laws.Tx, Bool.or(_, Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13))), Laws.TxWs{}, Laws.TxOut{}) ==
    Laws.TxOut{} : Laws.Tx}
  %s10 : {Bool.pick(Laws.Tx, Bool.or(_, U32.is_eq(uu, 13)), Laws.TxWs{}, Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}
  %s13 : {Bool.pick(Laws.Tx, _, Laws.TxWs{}, Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}
  {==}

# a word character outside strings keeps the scan outside
law tx_other:
  for +ch: Char
  for +h: {Lex.classify(ch) == Lex.COther{} : Lex.Class}
  {Laws.tx.step(Laws.TxOut{}, ch) == Laws.TxOut{} : Laws.Tx}

def tx_other(ch, h):
  match ch:
    case Chr{+uu}:
      tx_other.go(uu, M7.neq_cls(U32.is_eq(uu, 34), uu, 34, {==}, h, {==}), M7.neq_cls(U32.is_eq(uu, 32), uu, 32, {==},
          h,
        {==}),
        M7.neq_cls(U32.is_eq(uu, 9), uu, 9, {==}, h, {==}), M7.neq_cls(U32.is_eq(uu, 10), uu, 10, {==}, h, {==}),
        M7.neq_cls(U32.is_eq(uu, 13), uu, 13, {==}, h, {==}))

# word characters outside strings keep the scan outside
law tx_word:
  for +cs: List<&2, Char>
  for hw: M8.others(cs)
  {Laws.tx.run(cs, Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}

def tx_word(cs, hw):
  match cs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      (hc, ht) = hw
      Equal.trans(Laws.Tx, Laws.tx.run(tl, Laws.tx.step(Laws.TxOut{}, hd)), Laws.tx.run(tl, Laws.TxOut{}), Laws.TxOut{},
        Equal.cong(Laws.Tx, Laws.Tx, zz => Laws.tx.run(tl, zz), Laws.tx.step(Laws.TxOut{}, hd), Laws.TxOut{},
          tx_other(hd, hc)),
        tx_word(tl, ht))

# a JSON number keeps the scan outside strings
law tx_num:
  for +raw: String
  for h: {V.num.ok(raw) == True{} : Bool}
  {Laws.tx.run(String.to_list(raw), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}

def tx_num(raw, h):
  tx_word(String.to_list(raw), M3.oth_number(String.to_list(raw), Equal.trans(Bool, D1.number(String.to_list(raw)),
    V.num.ok(raw), True{}, Equal.sym(Bool, V.num.ok(raw), D1.number(String.to_list(raw)), L2.num_grammar(raw)), h)))

# what tx_ctl says of a code point: its \u00XX escape stays inside the string
def txu_goal(uu: U32) -> Type:
  {Laws.tx.run(String.to_list(Print.escape.u(uu)), Laws.TxIn{}) == Laws.TxIn{} : Laws.Tx}

# tx_ctl, one control at a time
law tx_ctl5:
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  txu_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, M7.zw(26n)}}}}}}})

def tx_ctl5(b0, b1, b2, b3, b4):
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

# tx_ctl, once bit 5 and the bits above are known
law tx_ctl.at:
  for cc: Cmp
  for b5: Bool
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for +rest: Word(26n)
  for ec: {Word.cmp(26n, rest, M7.zw(26n)) == cc : Cmp}
  for h_lt: {Cmp.is_lt(Word.cmp.fin(b5, True{}, cc)) == True{} : Bool}
  txu_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}})

def tx_ctl.at(cc, b5, b0, b1, b2, b3, b4, rest, ec, h_lt):
  match cc:
    case LT{}:
      ez = Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, rest, M7.zw(26n)), LT{}, ec)
      Empty.absurd(txu_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
        M1.true_false(Equal.trans(Bool, True{},
        Cmp.is_lt(Word.cmp(26n, rest, M7.zw(26n))), False{},
        Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, rest, M7.zw(26n))), True{}, ez), M7.zw_nlt(26n, rest))))
    case GT{}:
      match b5:
        case False{}:
          Empty.absurd(txu_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, rest}}}}}}}),
            M2.false_true(h_lt))
        case True{}:
          Empty.absurd(txu_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{}, rest}}}}}}}),
            M2.false_true(h_lt))
    case EQ{}:
      match b5:
        case True{}:
          Empty.absurd(txu_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{}, rest}}}}}}}),
            M2.false_true(h_lt))
        case False{}:
          er = Equal.sym(Word(26n), rest, M7.zw(26n),
            M7.weq(26n, rest, M7.zw(26n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(26n, rest, M7.zw(26n)),
                EQ{}, ec)))
          %er : txu_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, _}}}}}}})
          tx_ctl5(b0, b1, b2, b3, b4)

# a control below U+0020, written as \u00XX, stays inside the string
law tx_ctl:
  for +uu: U32
  for h_lt: {U32.is_lt(uu, 32) == True{} : Bool}
  txu_goal(uu)

def tx_ctl(uu, h_lt):
  match uu:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +rest}}}}}}}:
      +c5 = Word.cmp.fin(b5, True{}, Word.cmp(26n, rest, M7.zw(26n)))
      +c4 = Word.cmp.fin(b4, False{}, c5)
      +c3 = Word.cmp.fin(b3, False{}, c4)
      +c2 = Word.cmp.fin(b2, False{}, c3)
      +c1 = Word.cmp.fin(b1, False{}, c2)
      h5 = M7.lt_up(b4, c5, M7.lt_up(b3, c4, M7.lt_up(b2, c3, M7.lt_up(b1, c2, M7.lt_up(b0, c1, h_lt)))))
      tx_ctl.at(Word.cmp(26n, rest, M7.zw(26n)), b5, b0, b1, b2, b3, b4, rest, {==}, h5)

# escape.plain's answer, with its tests named, stays inside the string
law tx_plain:
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
  for ect: {U32.is_lt(uu, 32) == ct : Bool}
  {Laws.tx.run(String.to_list(Bool.pick(String, b34, "\\\"", Bool.pick(String, b92, "\\\\", Bool.pick(String, b8,
    "\\b", Bool.pick(String, b12, "\\f", Bool.pick(String, b10, "\\n", Bool.pick(String, b13, "\\r", Bool.pick(String,
    b9, "\\t", Print.escape.rest.go(uu, Chr{uu}, ct))))))))), Laws.TxIn{}) == Laws.TxIn{} : Laws.Tx}

def tx_plain(b34, b92, b8, b12, b10, b13, b9, ct, uu, e34, e92, ect):
  match b34:
    case True{}:
      {==}
    case False{}:
      match b92:
        case True{}:
          {==}
        case False{}:
          match b8:
            case True{}:
              {==}
            case False{}:
              match b12:
                case True{}:
                  {==}
                case False{}:
                  match b10:
                    case True{}:
                      {==}
                    case False{}:
                      match b13:
                        case True{}:
                          {==}
                        case False{}:
                          match b9:
                            case True{}:
                              {==}
                            case False{}:
                              match ct:
                                case True{}:
                                  tx_ctl(uu, ect)
                                case False{}:
                                  s92 = Equal.sym(Bool, U32.is_eq(uu, 92), False{}, e92)
                                  s34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, e34)
                                  %s92 : {Bool.pick(Laws.Tx, _, Laws.TxEsc{}, Bool.pick(Laws.Tx, U32.is_eq(uu, 34),
                                    Laws.TxOut{}, Laws.TxIn{})) == Laws.TxIn{} : Laws.Tx}
                                  %s34 : {Bool.pick(Laws.Tx, _, Laws.TxOut{}, Laws.TxIn{}) == Laws.TxIn{} : Laws.Tx}
                                  {==}

# one character's escape, once it is known whether it is a scalar value
law tx_sc:
  for sc: Bool
  for +uu: U32
  {Laws.tx.run(String.to_list(Print.escape.scalar(uu, Chr{uu}, sc)), Laws.TxIn{}) == Laws.TxIn{} : Laws.Tx}

def tx_sc(sc, uu):
  match sc:
    case True{}:
      tx_plain(U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_eq(uu, 8), U32.is_eq(uu, 12), U32.is_eq(uu, 10),
        U32.is_eq(uu, 13), U32.is_eq(uu, 9), U32.is_lt(uu, 32), uu, {==}, {==}, {==})
    case False{}:
      {==}

# a character print escapes stays inside the string
law tx_char:
  for +ch: Char
  {Laws.tx.run(String.to_list(Print.escape.char(ch)), Laws.TxIn{}) == Laws.TxIn{} : Laws.Tx}

def tx_char(ch):
  match ch:
    case Chr{+uu}:
      tx_sc(Print.scalar(uu), uu)

# print's escape of the characters stays inside the string
law tx_esc:
  for +cs: List<&2, Char>
  {Laws.tx.run(String.to_list(Print.escape(cs)), Laws.TxIn{}) == Laws.TxIn{} : Laws.Tx}

def tx_esc(cs):
  match cs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.escape.char(hd) ++ Print.escape(tl)), Laws.TxIn{}),
        Laws.tx.run(String.to_list(Print.escape(tl)), Laws.TxIn{}), Laws.TxIn{},
        tseq(Print.escape.char(hd), Print.escape(tl), Laws.TxIn{}, Laws.TxIn{}, tx_char(hd)), tx_esc(tl))

# a quoted string leaves the scan outside strings
law tx_quote:
  for +txt: String
  {Laws.tx.run(String.to_list(Print.quote(txt)), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}

def tx_quote(txt):
  +ee = Print.escape(String.to_list(txt))
  Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("\"" ++ ee ++ "\""), Laws.TxOut{}),
    Laws.tx.run(String.to_list(ee ++ "\""), Laws.TxIn{}), Laws.TxOut{},
    tseq("\"", ee ++ "\"", Laws.TxOut{}, Laws.TxIn{}, {==}),
    tseq(ee, "\"", Laws.TxIn{}, Laws.TxIn{}, tx_esc(String.to_list(txt))))

# tx_print for an array cell, by what follows it
law txp_cons:
  for tl: V.Json
  for +hd: V.Json
  for +h: {V.wf.go(V.JCons{hd, tl}, V.WArr{}) == True{} : Bool}
  for ih_hd: {V.wf.go(hd, V.WVal{}) == True{} : Bool} -> {Laws.tx.run(String.to_list(Print.print(hd)),
    Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}
  for ih_tl: {V.wf.go(tl, V.WArr{}) == True{} : Bool} -> {Laws.tx.run(String.to_list(Print.print(tl)),
    Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}
  {Laws.tx.run(String.to_list(Print.print(V.JCons{hd, tl})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}

def txp_cons(tl, hd, h, ih_hd, ih_tl):
  match tl:
    case V.JNil{}:
      ih_hd(M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNil{}, V.WArr{}), h))
    case V.JNull{}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNull{}))),
        Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JNull{})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(hd), "," ++ Print.print(V.JNull{}), Laws.TxOut{}, Laws.TxOut{}, ih_hd(M2.stop_l(V.wf.go(hd,
          V.WVal{}), V.wf.go(V.JNull{}, V.WArr{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JNull{})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JNull{})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JNull{}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_tl(M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNull{}, V.WArr{}), h))))
    case V.JBool{+t1}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBool{t1}))),
        Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JBool{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(hd), "," ++ Print.print(V.JBool{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_hd(M2.stop_l(V.wf.go(hd,
          V.WVal{}), V.wf.go(V.JBool{t1}, V.WArr{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JBool{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JBool{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JBool{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_tl(M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBool{t1}, V.WArr{}), h))))
    case V.JNum{+t1}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNum{t1}))),
        Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JNum{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(hd), "," ++ Print.print(V.JNum{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_hd(M2.stop_l(V.wf.go(hd,
          V.WVal{}), V.wf.go(V.JNum{t1}, V.WArr{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JNum{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JNum{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JNum{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_tl(M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNum{t1}, V.WArr{}), h))))
    case V.JStr{+t1}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JStr{t1}))),
        Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JStr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(hd), "," ++ Print.print(V.JStr{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_hd(M2.stop_l(V.wf.go(hd,
          V.WVal{}), V.wf.go(V.JStr{t1}, V.WArr{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JStr{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JStr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JStr{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_tl(M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JStr{t1}, V.WArr{}), h))))
    case V.JArr{+t1}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JArr{t1}))),
        Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JArr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(hd), "," ++ Print.print(V.JArr{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_hd(M2.stop_l(V.wf.go(hd,
          V.WVal{}), V.wf.go(V.JArr{t1}, V.WArr{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JArr{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JArr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JArr{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_tl(M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JArr{t1}, V.WArr{}), h))))
    case V.JObj{+t1}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JObj{t1}))),
        Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JObj{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(hd), "," ++ Print.print(V.JObj{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_hd(M2.stop_l(V.wf.go(hd,
          V.WVal{}), V.wf.go(V.JObj{t1}, V.WArr{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JObj{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JObj{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JObj{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_tl(M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JObj{t1}, V.WArr{}), h))))
    case V.JCons{+t1, +t2}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JCons{t1, t2}))),
        Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(hd), "," ++ Print.print(V.JCons{t1, t2}), Laws.TxOut{}, Laws.TxOut{},
            ih_hd(M2.stop_l(V.wf.go(hd,
          V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WArr{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JCons{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JCons{t1, t2}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_tl(M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WArr{}), h))))
    case V.JPair{+t1, +t2, +t3}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))),
        Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(hd), "," ++ Print.print(V.JPair{t1, t2, t3}), Laws.TxOut{}, Laws.TxOut{},
          ih_hd(M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WArr{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JPair{t1, t2, t3}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_tl(M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WArr{}), h))))
    case V.JSpan{+t1, +t2}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JSpan{t1, t2}))),
        Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(hd), "," ++ Print.print(V.JSpan{t1, t2}), Laws.TxOut{}, Laws.TxOut{},
            ih_hd(M2.stop_l(V.wf.go(hd,
          V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WArr{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JSpan{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JSpan{t1, t2}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_tl(M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WArr{}), h))))
    case V.JBind{+t1, +t2, +t3, +t4}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
        t4}))), Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})), Laws.TxOut{}),
        Laws.TxOut{},
        tseq(Print.print(hd), "," ++ Print.print(V.JBind{t1, t2, t3, t4}), Laws.TxOut{}, Laws.TxOut{},
          ih_hd(M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WArr{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JBind{t1, t2, t3, t4}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_tl(M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WArr{}), h))))

# tx_print for an object cell, by what follows it
law txp_pair:
  for rr: V.Json
  for +kk: String
  for +vv: V.Json
  for +h: {V.wf.go(V.JPair{kk, vv, rr}, V.WObj{}) == True{} : Bool}
  for ih_v: {V.wf.go(vv, V.WVal{}) == True{} : Bool} -> {Laws.tx.run(String.to_list(Print.print(vv)),
    Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}
  for ih_r: {V.wf.go(rr, V.WObj{}) == True{} : Bool} -> {Laws.tx.run(String.to_list(Print.print(rr)),
    Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}
  {Laws.tx.run(String.to_list(Print.print(V.JPair{kk, vv, rr})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}

def txp_pair(rr, kk, vv, h, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(kk) ++ (":" ++ Print.print(vv))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ Print.print(vv)), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(kk), ":" ++ Print.print(vv), Laws.TxOut{}, Laws.TxOut{}, tx_quote(kk)),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ Print.print(vv)), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(vv)), Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_v(M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h))))
    case V.JNull{}:
      Equal.trans(Laws.Tx,
        Laws.tx.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))),
        Laws.TxOut{}), Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))),
        Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(kk), ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(kk)),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Laws.TxOut{}),
          Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JNull{})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JNull{})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JNull{}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JNull{})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JNull{})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JNull{}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h))))))
    case V.JBool{+t1}:
      Equal.trans(Laws.Tx,
        Laws.tx.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))),
        Laws.TxOut{}), Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))),
        Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(kk), ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Laws.TxOut{},
          Laws.TxOut{}, tx_quote(kk)),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JBool{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JBool{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JBool{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JBool{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JBool{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h))))))
    case V.JNum{+t1}:
      Equal.trans(Laws.Tx,
        Laws.tx.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))),
        Laws.TxOut{}), Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))),
        Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(kk), ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(kk)),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JNum{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JNum{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JNum{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JNum{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JNum{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h))))))
    case V.JStr{+t1}:
      Equal.trans(Laws.Tx,
        Laws.tx.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))),
        Laws.TxOut{}), Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))),
        Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(kk), ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(kk)),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JStr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JStr{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JStr{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JStr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JStr{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h))))))
    case V.JArr{+t1}:
      Equal.trans(Laws.Tx,
        Laws.tx.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))),
        Laws.TxOut{}), Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))),
        Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(kk), ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(kk)),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JArr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JArr{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JArr{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JArr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JArr{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h))))))
    case V.JObj{+t1}:
      Equal.trans(Laws.Tx,
        Laws.tx.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))),
        Laws.TxOut{}), Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))),
        Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(kk), ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(kk)),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JObj{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JObj{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JObj{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JObj{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JObj{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h))))))
    case V.JCons{+t1, +t2}:
      Equal.trans(Laws.Tx,
        Laws.tx.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1,
        t2}))))), Laws.TxOut{}), Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1,
        t2})))), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(kk), ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Laws.TxOut{},
          Laws.TxOut{}, tx_quote(kk)),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1,
          t2})))), Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JCons{t1, t2}), Laws.TxOut{}, Laws.TxOut{},
            ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JCons{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JCons{t1, t2}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h))))))
    case V.JPair{+t1, +t2, +t3}:
      Equal.trans(Laws.Tx,
        Laws.tx.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
        t3}))))), Laws.TxOut{}), Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1,
        t2, t3})))), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(kk), ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Laws.TxOut{},
          Laws.TxOut{}, tx_quote(kk)),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
          t3})))), Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
          t3}))), Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), Laws.TxOut{}),
          Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JPair{t1, t2, t3}), Laws.TxOut{}, Laws.TxOut{},
          ih_v(M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JPair{t1, t2, t3}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h))))))
    case V.JSpan{+t1, +t2}:
      Equal.trans(Laws.Tx,
        Laws.tx.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1,
        t2}))))), Laws.TxOut{}), Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1,
        t2})))), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(kk), ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Laws.TxOut{},
          Laws.TxOut{}, tx_quote(kk)),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1,
          t2})))), Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JSpan{t1, t2}), Laws.TxOut{}, Laws.TxOut{},
            ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JSpan{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JSpan{t1, t2}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h))))))
    case V.JBind{+t1, +t2, +t3, +t4}:
      Equal.trans(Laws.Tx,
        Laws.tx.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2,
        t3, t4}))))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})))),
        Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(kk), ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Laws.TxOut{},
          Laws.TxOut{}, tx_quote(kk)),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2,
          t3, t4})))), Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2,
          t3, t4}))), Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
          t4}))), Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JBind{t1, t2, t3, t4}), Laws.TxOut{}, Laws.TxOut{},
          ih_v(M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JBind{t1, t2, t3, t4}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h))))))

# tx_print for an object cell, by what follows it
law txp_bind:
  for rr: V.Json
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for +h: {V.wf.go(V.JBind{src, nn, vv, rr}, V.WObj{}) == True{} : Bool}
  for ih_v: {V.wf.go(vv, V.WVal{}) == True{} : Bool} -> {Laws.tx.run(String.to_list(Print.print(vv)),
    Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}
  for ih_r: {V.wf.go(rr, V.WObj{}) == True{} : Bool} -> {Laws.tx.run(String.to_list(Print.print(rr)),
    Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}
  {Laws.tx.run(String.to_list(Print.print(V.JBind{src, nn, vv, rr})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}

def txp_bind(rr, src, nn, vv, h, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ Print.print(vv))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ Print.print(vv)), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))), ":" ++ Print.print(vv), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ Print.print(vv)), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(vv)), Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_v(M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h))))
    case V.JNull{}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))), Laws.TxOut{}),
        Laws.TxOut{},
        tseq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Laws.TxOut{}),
          Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JNull{})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JNull{})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JNull{}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JNull{})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JNull{})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JNull{}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h))))))
    case V.JBool{+t1}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))), Laws.TxOut{}),
        Laws.TxOut{},
        tseq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JBool{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JBool{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JBool{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JBool{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JBool{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h))))))
    case V.JNum{+t1}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))), Laws.TxOut{}),
        Laws.TxOut{},
        tseq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JNum{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JNum{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JNum{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JNum{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JNum{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h))))))
    case V.JStr{+t1}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))), Laws.TxOut{}),
        Laws.TxOut{},
        tseq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JStr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JStr{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JStr{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JStr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JStr{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h))))))
    case V.JArr{+t1}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))), Laws.TxOut{}),
        Laws.TxOut{},
        tseq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JArr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JArr{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JArr{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JArr{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JArr{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h))))))
    case V.JObj{+t1}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))), Laws.TxOut{}),
        Laws.TxOut{},
        tseq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))),
          Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JObj{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JObj{t1}), Laws.TxOut{}, Laws.TxOut{}, ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JObj{t1})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JObj{t1})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JObj{t1}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h))))))
    case V.JCons{+t1, +t2}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})))), Laws.TxOut{}),
        Laws.TxOut{},
        tseq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1,
          t2})))), Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JCons{t1, t2}), Laws.TxOut{}, Laws.TxOut{},
            ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JCons{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JCons{t1, t2}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h))))))
    case V.JPair{+t1, +t2, +t3}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})))),
        Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
          t3})))), Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
          t3}))), Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), Laws.TxOut{}),
          Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JPair{t1, t2, t3}), Laws.TxOut{}, Laws.TxOut{},
          ih_v(M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JPair{t1, t2, t3}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h))))))
    case V.JSpan{+t1, +t2}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))))), Laws.TxOut{}),
        Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})))), Laws.TxOut{}),
        Laws.TxOut{},
        tseq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1,
          t2})))), Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))),
          Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JSpan{t1, t2}), Laws.TxOut{}, Laws.TxOut{},
            ih_v(M2.stop_l(V.wf.go(vv,
          V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JSpan{t1, t2})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JSpan{t1, t2}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h))))))
    case V.JBind{+t1, +t2, +t3, +t4}:
      Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))))),
        Laws.TxOut{}), Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
        t4})))), Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Laws.TxOut{}, Laws.TxOut{},
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2,
          t3, t4})))), Laws.TxOut{}), Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2,
          t3, t4}))), Laws.TxOut{}), Laws.TxOut{},
        tseq(":", Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})), Laws.TxOut{}, Laws.TxOut{}, {==}),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
          t4}))), Laws.TxOut{}), Laws.tx.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})),
          Laws.TxOut{}), Laws.TxOut{},
        tseq(Print.print(vv), "," ++ Print.print(V.JBind{t1, t2, t3, t4}), Laws.TxOut{}, Laws.TxOut{},
          ih_v(M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h))),
        Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})), Laws.TxOut{}),
          Laws.tx.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Laws.TxOut{}), Laws.TxOut{},
        tseq(",", Print.print(V.JBind{t1, t2, t3, t4}), Laws.TxOut{}, Laws.TxOut{}, {==}),
        ih_r(M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h))))))

# tx_print for a boolean
law txp_bool:
  for bb: Bool
  {Laws.tx.run(String.to_list(Print.print(V.JBool{bb})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}

def txp_bool(bb):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a well-formed value's text leaves the scan outside strings, never at
# whitespace
law tx_print:
  for +val: V.Json
  for +sh: V.Shape
  for +h: {V.wf.go(val, sh) == True{} : Bool}
  {Laws.tx.run(String.to_list(Print.print(val)), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}

def tx_print(val, sh, h):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JNull{})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WObj{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JNull{})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
    case V.JBool{bb}:
      match sh:
        case V.WVal{}:
          txp_bool(bb)
        case V.WArr{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JBool{bb})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WObj{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JBool{bb})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
    case V.JNum{+raw}:
      match sh:
        case V.WVal{}:
          tx_num(raw, h)
        case V.WArr{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JNum{raw})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WObj{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JNum{raw})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
    case V.JStr{+txt}:
      match sh:
        case V.WVal{}:
          tx_quote(txt)
        case V.WArr{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JStr{txt})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WObj{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JStr{txt})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
    case V.JArr{+items}:
      match sh:
        case V.WVal{}:
          Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("[" ++ (Print.print(items) ++ "]")), Laws.TxOut{}),
            Laws.tx.run(String.to_list(Print.print(items) ++ "]"), Laws.TxOut{}), Laws.TxOut{},
            tseq("[", Print.print(items) ++ "]", Laws.TxOut{}, Laws.TxOut{}, {==}),
            Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(items) ++ "]"), Laws.TxOut{}),
              Laws.tx.run(String.to_list("]"), Laws.TxOut{}), Laws.TxOut{},
            tseq(Print.print(items), "]", Laws.TxOut{}, Laws.TxOut{}, tx_print(items, V.WArr{}, h)),
            {==}))
        case V.WArr{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JArr{items})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WObj{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JArr{items})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
    case V.JObj{+pairs}:
      match sh:
        case V.WVal{}:
          Equal.trans(Laws.Tx, Laws.tx.run(String.to_list("{" ++ (Print.print(pairs) ++ "}")), Laws.TxOut{}),
            Laws.tx.run(String.to_list(Print.print(pairs) ++ "}"), Laws.TxOut{}), Laws.TxOut{},
            tseq("{", Print.print(pairs) ++ "}", Laws.TxOut{}, Laws.TxOut{}, {==}),
            Equal.trans(Laws.Tx, Laws.tx.run(String.to_list(Print.print(pairs) ++ "}"), Laws.TxOut{}),
              Laws.tx.run(String.to_list("}"), Laws.TxOut{}), Laws.TxOut{},
            tseq(Print.print(pairs), "}", Laws.TxOut{}, Laws.TxOut{}, tx_print(pairs, V.WObj{}, h)),
            {==}))
        case V.WArr{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JObj{pairs})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WObj{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JObj{pairs})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JNil{})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JCons{+hd, +tl}:
      match sh:
        case V.WVal{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JCons{hd, tl})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WArr{}:
          txp_cons(tl, hd, h, xx => tx_print(hd, V.WVal{}, xx), xx => tx_print(tl, V.WArr{}, xx))
        case V.WObj{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JCons{hd, tl})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
    case V.JPair{+kk, +vv, +rr}:
      match sh:
        case V.WVal{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JPair{kk, vv, rr})),
              Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WArr{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JPair{kk, vv, rr})),
              Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WObj{}:
          txp_pair(rr, kk, vv, h, xx => tx_print(vv, V.WVal{}, xx), xx => tx_print(rr, V.WObj{}, xx))
    case V.JSpan{+src, +nn}:
      match sh:
        case V.WVal{}:
          tx_quote(V.span.str(src, nn, U32.is_zero(nn)))
        case V.WArr{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JSpan{src, nn})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WObj{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JSpan{src, nn})), Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
    case V.JBind{+src, +nn, +vv, +rr}:
      match sh:
        case V.WVal{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JBind{src, nn, vv, rr})),
            Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WArr{}:
          M2.no({Laws.tx.run(String.to_list(Print.print(V.JBind{src, nn, vv, rr})),
            Laws.TxOut{}) == Laws.TxOut{} : Laws.Tx}, h)
        case V.WObj{}:
          txp_bind(rr, src, nn, vv, h, xx => tx_print(vv, V.WVal{}, xx), xx => tx_print(rr, V.WObj{}, xx))

# laws/PrintIsCompactAndStable.bend, the first half
def Laws.print_compact(txt, jj, e_p):
  hw = Equal.trans(Bool, V.wf(jj), L1.wf_m(Ezjson.parse(txt)), True{},
    Equal.sym(Bool, L1.wf_m(Ezjson.parse(txt)), V.wf(jj), Equal.cong(Maybe<&2, V.Json>, Bool, zz => L1.wf_m(zz),
      Ezjson.parse(txt), Some{jj}, e_p)), L1.parse_wf(txt))
  Equal.cong(Laws.Tx, Bool, zz => Laws.tx.ok(zz), Laws.tx.run(String.to_list(Print.print(jj)), Laws.TxOut{}),
    Laws.TxOut{}, tx_print(jj, V.WVal{}, hw))
