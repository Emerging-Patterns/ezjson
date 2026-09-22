# ezjson: the laws. Closed equalities from parse/print/query; PROOF.bend fills them.
import Base
import ./value.bend as V
import ./lex.bend as Lex
import ./parse.bend as Parse
import ./print.bend as Print
import ./lazy.bend as Lazy
import ./main.bend as Ezjson
import ./pull.bend as Pull

# parse then print; a failure is "<bad>"
def again(text: String) -> String:
  Print.maybe(Parse.parse(text))

# a built JSON message
def msg() -> V.Json:
  V.obj([("id", V.num("7")), ("method", V.JStr{"open"}),
    ("params", V.obj([("uri", V.JStr{"file:///a.bend"}),
      ("tags", V.arr([V.JNull{}, V.JBool{True{}}]))]))])

# a parse result or JNull
def parsed(m: Maybe<&2, V.Json>) -> V.Json:
  Maybe.default(&2, V.Json, m, V.JNull{})

# LAW: RFC 8259 §3 — null round-trips
law roundtrip_null:
  {again("null") == "null" : String}

# LAW: RFC 8259 §3 — true and false round-trip
law roundtrip_bools:
  {again("[true,false]") == "[true,false]" : String}

# LAW: RFC 8259 §6 — numbers keep their spelling
law roundtrip_nums:
  {again("[0,-12,3.50,1e9]") == "[0,-12,3.50,1e9]" : String}

# LAW: RFC 8259 §2 — space, tab, and line feed inside a value are insignificant
law roundtrip_space:
  {again(" { \"a\" : [ 1 , 2 ] ,\n\t\"b\" : { } } ") == "{\"a\":[1,2],\"b\":{}}" : String}

# LAW: RFC 8259 §7 — escapes decode and reprint
law roundtrip_escapes:
  {again("\"q\\\" b\\\\ n\\n t\\t u\\u0041\"") ++ again("\"\\b\\f\\/\\u0001\"")
    == "\"q\\\" b\\\\ n\\n t\\t uA\"" ++ "\"\\b\\f/\\u0001\"" : String}

# LAW: nesting round-trips
law roundtrip_nest:
  {again("[[[]],{\"k\":{\"k\":[null]}}]") == "[[[]],{\"k\":{\"k\":[null]}}]" : String}

# LAW: empty input is bad
law parse_empty:
  {again("") == "<bad>" : String}

# LAW: an unclosed array is bad
law parse_unclosed_arr:
  {again("[1,2") == "<bad>" : String}

# LAW: a stray close is bad
law parse_stray:
  {again("]") == "<bad>" : String}

# LAW: RFC 8259 §2 — two values are not one JSON text
law parse_two_roots:
  {again("1 2") == "<bad>" : String}

# LAW: an unclosed string is bad
law parse_unclosed_str:
  {again("\"abc") == "<bad>" : String}

# LAW: a mismatched close is bad
law parse_mismatch:
  {again("[}") == "<bad>" : String}

# LAW: a built value prints
law print_msg:
  {Print.print(msg()) ==
    "{\"id\":7,\"method\":\"open\",\"params\":{\"uri\":\"file:///a.bend\",\"tags\":[null,true]}}" : String}

# LAW: a path reads a string
law get_uri:
  {V.as_str(V.get(V.get(msg(), "params"), "uri")) == Some{"file:///a.bend"} : Maybe<&2, String>}

# LAW: a number reads
law get_id:
  {V.as_u32(V.get(msg(), "id")) == Some{7} : Maybe<&2, U32>}

# LAW: a missing key reads as none
law get_missing:
  {V.as_str(V.get(V.get(msg(), "nope"), "uri")) == None{} : Maybe<&2, String>}

# LAW: a string is not a number
law get_not_num:
  {V.as_u32(V.get(msg(), "method")) == None{} : Maybe<&2, U32>}

# LAW: parsed text at a is an object, not a string
law parse_obj_not_str:
  {V.as_str(V.get(parsed(Parse.parse("{\"a\":{\"b\":\"deep\"}}")), "a")) == None{} : Maybe<&2, String>}

# LAW: parsed paths chain
law parse_path_chain:
  {V.as_str(V.get(V.get(parsed(Parse.parse("{\"a\":{\"b\":\"deep\"}}")), "a"), "b"))
    == Some{"deep"} : Maybe<&2, String>}

# LAW: an array's first item
law arr_first:
  {Print.print(V.at(V.arr([V.null(), V.num("1")]), 0)) == "null" : String}

# LAW: find on a missing key is JNull
law find_missing:
  {V.as_str(V.find(V.JNil{}, "k")) == None{} : Maybe<&2, String>}

# LAW: reverse of no cells is the acc
law reverse_nil:
  {Print.print(V.reverse(V.JNil{}, V.JNull{})) == "null" : String}

# LAW: a quoted string
law print_quote:
  {Print.quote("a") == "\"a\"" : String}

# LAW: escape of a quote
law print_escape:
  {Print.escape(['"']) == "\\\"" : String}

# LAW: RFC 8259 §3 — null is the lowercase word
law parse_word_null:
  {Print.print(Parse.word("null")) == "null" : String}

# LAW: RFC 8259 §3 — true is the lowercase word
law parse_word_true:
  {Print.print(Parse.word("true")) == "true" : String}

# LAW: RFC 8259 §3 — false is the lowercase word
law parse_word_false:
  {Print.print(Parse.word("false")) == "false" : String}

# LAW: a number word keeps its text
law parse_word_num:
  {Print.print(Parse.word("3.50")) == "3.50" : String}

# LAW: finish of a good root
law parse_finish:
  {Print.maybe(Parse.finish(Parse.run(Lex.tokens("null"), Parse.P{False{}, None{}, []})))
    == "null" : String}

# LAW: result of a bad parse is none
law parse_result_bad:
  {Print.maybe(Parse.result(True{}, [], Some{V.JNull{}})) == "<bad>" : String}

# LAW: close_arr of an empty stack is bad
law parse_close_arr_empty:
  {Print.maybe(Parse.finish(Parse.close_arr([], None{}, False{}))) == "<bad>" : String}

# LAW: close_obj of an empty stack is bad
law parse_close_obj_empty:
  {Print.maybe(Parse.finish(Parse.close_obj([], None{}, False{}))) == "<bad>" : String}

# LAW: put of a value as the root
law parse_put_root:
  {Print.maybe(Parse.finish(Parse.put([], None{}, V.JNull{}, False{}))) == "null" : String}

# LAW: one token as the root
law parse_step_word:
  {Print.maybe(Parse.finish(Parse.step(Lex.TWord{"null"}, Parse.P{False{}, None{}, []})))
    == "null" : String}

# LAW: lex text of a reversed buffer
law lex_text:
  {Lex.text(['b', 'a']) == "ab" : String}

# LAW: n unescapes to newline
law lex_unescape_n:
  {Char.to_u32(Maybe.default(&2, Char, Lex.unescape('n'), '?')) == 10 : U32}

# LAW: hex of A is 10
law lex_hex_A:
  {Lex.hex('A') == 10 : U32}

# LAW: classify of space is CSpace
law lex_classify_space:
  {Lex.classify(' ') == Lex.CSpace{} : Lex.Class}

# LAW: parse is finish of run of tokens
law lex_tokens_null:
  {Print.maybe(Parse.parse("null")) == Print.maybe(Parse.finish(Parse.run(Lex.tokens("null"),
    Parse.P{False{}, None{}, []}))) : String}

# LAW: feed of a digit starts a word
law lex_feed_digit:
  {Lex.feed('1', Lex.Lex{Lex.Idle{}, [], []}) == Lex.Lex{Lex.Word{}, ['1'], []} : Lex.Lex}

# LAW: run of no chars is the state
law lex_run_empty:
  {Lex.run([], Lex.Lex{Lex.Idle{}, [], []}) == Lex.Lex{Lex.Idle{}, [], []} : Lex.Lex}

# LAW: step of a quote starts a string
law lex_step_quote:
  {Lex.step(Lex.Idle{}, Lex.classify('"'), '"', [], [])
    == Lex.Lex{Lex.Str{}, [], []} : Lex.Lex}

# LAW: escape of n in a string
law lex_escape_n:
  {Lex.escape('n', [], []) == Lex.Lex{Lex.Str{}, ['\n'], []} : Lex.Lex}

# LAW: unicode of the last hex digit
law lex_unicode:
  {Lex.unicode(0n, 0, 'A', [], []) == Lex.Lex{Lex.Str{}, [Char.from_u32(10)], []} : Lex.Lex}

# LAW: finish of an idle lexer is no tokens
law lex_finish_idle:
  {List.is_empty(&2, Lex.Tok, Lex.finish(Lex.Lex{Lex.Idle{}, [], []})) == True{} : Bool}

# LAW: RFC 8259 §4 — an empty object prints
law value_obj:
  {Print.print(V.obj([])) == "{}" : String}

# LAW: stop takes the value when true
law lazy_stop_true:
  {Lazy.stop(U32, True{}, 1, _u => 2) == 1 : U32}

# LAW: the public parse
law public_parse:
  {Print.maybe(Ezjson.parse("null")) == "null" : String}

# LAW: the public print
law public_print:
  {Ezjson.print(V.JNull{}) == "null" : String}

# LAW: the public obj
law public_obj:
  {Ezjson.print(Ezjson.obj([])) == "{}" : String}

# LAW: RFC 8259 §5 — an empty array prints
law public_arr:
  {Ezjson.print(Ezjson.arr([])) == "[]" : String}

# LAW: the public num keeps a JSON number and drops any other text
law public_num:
  {Ezjson.print(Ezjson.num("3.50")) ++ Print.print(V.num("01")) == "3.50null" : String}

# LAW: the public get
law public_get:
  {Ezjson.as_str(Ezjson.get(Ezjson.obj([("k", Ezjson.str("v"))]), "k"))
    == Some{"v"} : Maybe<&2, String>}

# LAW: RFC 8259 §4 and §5 — a missing comma, a trailing comma, a missing colon,
# and a trailing root comma are rejected
law parse_seps:
  {again("[1,2]") ++ again("[1 2]") ++ again("[1,]") ++ again("{\"a\":1}")
    ++ again("{\"a\" 1}") ++ again("{\"a\":1,}") ++ again("1,")
    == "[1,2]<bad><bad>{\"a\":1}<bad><bad><bad>" : String}

# LAW: RFC 8259 §6 — a number keeps its spelling; a leading zero, a bare minus,
# a trailing dot, and a leading plus are rejected
law parse_number:
  {again("[-0,1e+2,3.50]") ++ again("01") ++ again("-") ++ again("1.") ++ again("+1")
    == "[-0,1e+2,3.50]<bad><bad><bad><bad>" : String}

# LAW: RFC 8259 §7 and §8.2 — a bad escape, a short \\u, a raw line feed, and a
# lone surrogate are rejected
law parse_bad_text:
  {again("\"\\a\"") ++ again("\"\\u12\"") ++ again("\"\\uXXXX\"") ++ again("\"\n\"")
    ++ again("\"\\uDEAD\"") ++ again("\"\\uD800\"")
    == "<bad><bad><bad><bad><bad><bad>" : String}

def code.go(m: Maybe<&2, Char>) -> U32:
  match m:
    case None{}:
      0
    case Some{c}:
      Char.to_u32(c)

# the code point of a string's first char, or 0
def code(s: String) -> U32:
  code.go(String.get(s, 0n))

# LAW: RFC 8259 §7 — a surrogate pair is one code point
law parse_surrogate:
  {code(Maybe.default(&2, String, V.as_str(parsed(Parse.parse("\"\\uD800\\uDC00\""))), ""))
    == 65536 : U32}

# LAW: the public null
law public_null:
  {Ezjson.print(Ezjson.null()) == Print.print(V.null()) : String}

# LAW: the public bool
law public_bool:
  {Ezjson.print(Ezjson.bool(False{})) ++ Print.print(V.bool(True{})) == "falsetrue" : String}

# LAW: the public str
law public_str:
  {Maybe.default(&2, String, Ezjson.as_str(Ezjson.str("a")), "")
    ++ Maybe.default(&2, String, V.as_str(V.str("b")), "") == "ab" : String}

# LAW: the public at
law public_at:
  {Ezjson.as_str(Ezjson.at(Ezjson.arr([Ezjson.str("z")]), 0))
    == V.as_str(V.at(V.arr([V.str("z")]), 0)) : Maybe<&2, String>}

# LAW: the public as_bool
law public_as_bool:
  {Ezjson.as_bool(Ezjson.bool(True{})) == V.as_bool(V.bool(True{})) : Maybe<&2, Bool>}

# LAW: the public as_num
law public_as_num:
  {Maybe.default(&2, String, Ezjson.as_num(Ezjson.num("-2")), "")
    ++ Maybe.default(&2, String, V.as_num(V.null()), "x") == "-2x" : String}

# LAW: the public as_u32
law public_as_u32:
  {U32.add(Maybe.default(&2, U32, Ezjson.as_u32(Ezjson.num("7")), 0),
    Maybe.default(&2, U32, V.as_u32(V.num("-2")), 3)) == 10 : U32}

# LAW: the public as_f32
law public_as_f32:
  {Ezjson.as_f32(Ezjson.num("1.5")) == V.as_f32(V.num("1.5")) : Maybe<&2, F32>}

# the kind of a parse result: null, true, false, num, str, arr, obj, or bad
def kind.go(m: Maybe<&2, V.Json>) -> String:
  match m:
    case None{}:
      "bad"
    case Some{V.JNull{}}:
      "null"
    case Some{V.JBool{True{}}}:
      "true"
    case Some{V.JBool{False{}}}:
      "false"
    case Some{V.JNum{raw}}:
      "num:" ++ raw
    case Some{V.JStr{text}}:
      "str:" ++ text
    case Some{V.JSpan{src, +n}}:
      "str:" ++ V.span.str(src, n, U32.is_zero(n))
    case Some{V.JArr{items}}:
      "arr:" ++ Print.print(V.JArr{items})
    case Some{V.JObj{pairs}}:
      "obj:" ++ Print.print(V.JObj{pairs})
    case Some{other}:
      "bad"

# the kind of one JSON text
def kind(s: String) -> String:
  kind.go(Parse.parse(s))

# LAW: RFC 8259 §3 — null, true, false, a number, a string, an array, and an
# object parse as those kinds
law rfc_values:
  {kind("null") ++ kind("true") ++ kind("false") ++ kind("-0") ++ kind("\"a\"")
    ++ kind("[]") ++ kind("{}")
    == "nulltruefalsenum:-0str:aarr:[]obj:{}" : String}

# LAW: RFC 8259 §3 — true, false, and null are lowercase, and a longer word is
# not one of them
law rfc_literals:
  {again("True") ++ again("TRUE") ++ again("False") ++ again("FALSE")
    ++ again("Null") ++ again("NULL") ++ again("truex") ++ again("nul")
    ++ again("True ")
    == "<bad><bad><bad><bad><bad><bad><bad><bad><bad>" : String}

# LAW: RFC 8259 §2 — space, tab, line feed, and carriage return are insignificant
law rfc_ws:
  {again(" \t\r\n[ \t]\r\n") ++ again("{ \n\t\r}") ++ again("[\n1\r,\t2 ]")
    == "[]{}[1,2]" : String}

# a one-character string of code point n, in quotes
def quoted_cp(n: U32) -> String:
  "\"" ++ String.from_list([Char.from_u32(n)]) ++ "\""

# brackets around the character of code point n
def bracket_cp(n: U32) -> String:
  "[" ++ String.from_list([Char.from_u32(n)]) ++ "]"

# s, left times
def repeat(left: Nat, +s: String) -> String:
  match left:
    case 0n:
      ""
    case 1n+p:
      s ++ repeat(p, s)

# parse of a string holding each code point from n, for left points
def scan_raw(left: Nat, +n: U32) -> String:
  match left:
    case 0n:
      ""
    case 1n+p:
      again(quoted_cp(n)) ++ scan_raw(p, U32.add(n, 1))

# LAW: RFC 8259 §7 — a raw U+0000 through U+001F in a string is rejected
law rfc_raw_controls:
  {scan_raw(32n, 0) == repeat(32n, "<bad>") : String}

# tab, line feed, or carriage return
def is_ws_ctl(+n: U32) -> Bool:
  Bool.or(U32.is_eq(n, 9), Bool.or(U32.is_eq(n, 10), U32.is_eq(n, 13)))

# parse of brackets around each code point from n, for left points
def scan_ws(left: Nat, +n: U32) -> String:
  match left:
    case 0n:
      ""
    case 1n+p:
      again(bracket_cp(n)) ++ scan_ws(p, U32.add(n, 1))

# "[]" where n is tab, line feed, or carriage return, else "<bad>"
def expect_ws(left: Nat, +n: U32) -> String:
  match left:
    case 0n:
      ""
    case 1n+p:
      Bool.pick(String, is_ws_ctl(n), "[]", "<bad>") ++ expect_ws(p, U32.add(n, 1))

# LAW: RFC 8259 §2 — among U+0000 through U+001F, only tab, line feed, and
# carriage return are whitespace. U+000B and U+000C are not.
law rfc_ws_ctl:
  {scan_ws(32n, 0) == expect_ws(32n, 0) : String}

# LAW: RFC 8259 §2 — a text is one value, with whitespace only around that value
law rfc_one:
  {again(" \t\r\ntrue\r\n\t ") ++ again("true false") ++ again("[][]")
    ++ again("null,")
    == "true<bad><bad><bad>" : String}

# one hex nibble, lowercase
def nib.go(+n: U32, digit: Bool) -> Char:
  match digit:
    case True{}:
      Char.from_u32(U32.add(48, n))
    case False{}:
      Char.from_u32(U32.add(87, n))

# one hex nibble, lowercase
def nib(+n: U32) -> Char:
  nib.go(n, U32.is_lt(n, 10))

# the JSON text of a \\u00XX escape of n, in quotes
def u_text(+n: U32) -> String:
  "\"\\u00" ++ String.from_list([nib(U32.div(n, 16)), nib(U32.mod(n, 16))]) ++ "\""

# the code point of a parsed string, or 65535 when the text is not one
def u_point.go(m: Maybe<&2, V.Json>) -> U32:
  match m:
    case Some{V.JStr{s}}:
      code(s)
    case Some{V.JSpan{src, +n}}:
      code(V.span.str(src, n, U32.is_zero(n)))
    case other:
      65535

# the code point a \\u escape parses as, or 65535 when it is not a string
def u_point(n: U32) -> U32:
  u_point.go(Parse.parse(u_text(n)))

# each \\u escape from n, for left points, is that code point
def scan_u(left: Nat, +n: U32) -> Bool:
  match left:
    case 0n:
      True{}
    case 1n+p:
      Lazy.stop(Bool, U32.is_eq(u_point(n), n), scan_u(p, U32.add(n, 1)), _u => False{})

# LAW: RFC 8259 §7 — \\u0000 through \\u001F are those code points
law rfc_u_controls:
  {scan_u(32n, 0) == True{} : Bool}

# LAW: RFC 8259 §7 — quote, reverse solidus, solidus, and the short controls
# escape, and \\u reprints the decoded character
law rfc_escapes:
  {again("\"\\\"\\\\\\/\\b\\f\\n\\r\\t\\u0000\\u001F\"")
    == "\"\\\"\\\\/\\b\\f\\n\\r\\t\\u0000\\u001f\"" : String}

# a quoted code point, as print writes it
def qcp(n: U32) -> String:
  Print.quote(String.from_list([Char.from_u32(n)]))

# LAW: RFC 8259 §7 and §10 — print escapes U+0000 through U+001F
law rfc_gen_ctrl:
  {qcp(0) ++ qcp(8) ++ qcp(9) ++ qcp(10) ++ qcp(12) ++ qcp(13) ++ qcp(31)
    == "\"\\u0000\"\"\\b\"\"\\t\"\"\\n\"\"\\f\"\"\\r\"\"\\u001f\"" : String}

# the characters of a parsed string, or empty when it is not one
def str_of(s: String) -> String:
  Maybe.default(&2, String, V.as_str(parsed(Parse.parse(s))), "")

# LAW: RFC 8259 §8.3 — escaped and unescaped spellings of one string compare equal
law rfc_cmp:
  {str_of("\"a\\\\b\"") ++ str_of("\"a\\u005Cb\"") ++ str_of("\"a\\u005cb\"")
    ++ str_of("\"\\u0041\"") ++ str_of("\"A\"")
    == "a\\ba\\ba\\bAA" : String}

# LAW: RFC 8259 §8.3 — an object name compares as its decoded characters
law rfc_name:
  {V.as_u32(V.get(parsed(Parse.parse("{\"a\\u0042\":3}")), "aB"))
    == Some{3} : Maybe<&2, U32>}

# LAW: RFC 8259 §6 — a JSON number keeps its spelling. NaN, Infinity, a leading
# plus, and a leading zero are not numbers.
law rfc_numbers:
  {again("[0,-0,0.0,0e1,0E+1,1E-2,1e+2,3.50]")
    ++ again("NaN") ++ again("Infinity") ++ again("+Infinity") ++ again("-Infinity")
    ++ again("01") ++ again("-01") ++ again("00") ++ again("+1") ++ again("+0")
    ++ again("1.") ++ again(".1") ++ again("-.1") ++ again("1e") ++ again("1e+")
    ++ again("1e-") ++ again("0x1") ++ again("--1") ++ again("01.2")
    ++ Print.print(Ezjson.num("NaN")) ++ Print.print(Ezjson.num("Infinity"))
    ++ Print.print(Ezjson.num("+Infinity")) ++ Print.print(Ezjson.num("-Infinity"))
    ++ Print.print(Ezjson.num("01")) ++ Print.print(Ezjson.num("-01"))
    ++ Print.print(Ezjson.num("+1")) ++ Print.print(Ezjson.num("0"))
    ++ Print.print(Ezjson.num("-0"))
    == "[0,-0,0.0,0e1,0E+1,1E-2,1e+2,3.50]<bad><bad><bad><bad><bad><bad><bad><bad><bad><bad><bad><bad><bad><bad><bad><bad><bad><bad>nullnullnullnullnullnullnull0-0" : String}

# LAW: RFC 8259 §4 and §5 — an empty object and an empty array are values, a
# name is a string, and a trailing comma is rejected
law rfc_struct:
  {again("[]") ++ again("{}") ++ again("[1,2]") ++ again("{\"a\":1,\"\":0}")
    ++ again("[null,true,1,\"a\",[],{}]")
    ++ again("[1,]") ++ again("{\"a\":1,}") ++ again("{a:1}") ++ again("{1:2}")
    ++ again("[1,,2]") ++ again("[,]") ++ again("{,}")
    == "[]{}[1,2]{\"a\":1,\"\":0}[null,true,1,\"a\",[],{}]<bad><bad><bad><bad><bad><bad><bad>" : String}

# LAW: RFC 8259 §7 — U+2028 and U+2029 may occur unescaped in a string
law rfc_line_sep:
  {again("\"" ++ String.from_list([Char.from_u32(8232), Char.from_u32(8233)]) ++ "\"")
    == "\"" ++ String.from_list([Char.from_u32(8232), Char.from_u32(8233)]) ++ "\"" : String}

# LAW: RFC 8259 §8.1 — a leading U+FEFF is not whitespace, and print does not
# emit one
law rfc_bom:
  {again(String.from_list([Char.from_u32(65279)]) ++ "null") ++ Print.print(V.JNull{})
    == "<bad>null" : String}

# one pull event, as a short tag. A span and an owned string tag the same
def pull.tag(ev: Pull.Ev) -> String:
  match ev:
    case Pull.ENull{}:
      "null"
    case Pull.EBool{True{}}:
      "true"
    case Pull.EBool{False{}}:
      "false"
    case Pull.ENum{src, +nn}:
      "#" ++ V.span.str(src, nn, U32.is_zero(nn))
    case Pull.EStr{body}:
      "s:" ++ body
    case Pull.EStrS{src, +nn}:
      "s:" ++ V.span.str(src, nn, U32.is_zero(nn))
    case Pull.EKey{body}:
      "k:" ++ body
    case Pull.EKeyS{src, +nn}:
      "k:" ++ V.span.str(src, nn, U32.is_zero(nn))
    case Pull.EBeginArr{}:
      "["
    case Pull.EEndArr{}:
      "]"
    case Pull.EBeginObj{}:
      "{"
    case Pull.EEndObj{}:
      "}"
    case Pull.EEnd{}:
      "."
    case Pull.EErr{}:
      "!"

# the walk: still need an event, or holding one
type PullPh is Data:
  PullNeed{cur: Pull.Cur, acc: String}
  PullHave{ev: Pull.Ev, cur: Pull.Cur, acc: String}

# an event just read, kept with the text so far
def pull.pack(acc: String, got: (Pull.Ev & Pull.Cur)) -> PullPh:
  (ev, cur) = got
  PullHave{ev, cur, acc}

# enough steps to read one event per character, plus the end
def pull.fuel(+src: String) -> Nat:
  1n+Nat.add(String.length(src), String.length(src))

# every event, in order, until the end or the first error
def pull.drain(left: Nat, ph: PullPh) -> String:
  match left ph:
    case n PullHave{Pull.EEnd{}, cur, acc}:
      acc ++ "."
    case n PullHave{Pull.EErr{}, cur, acc}:
      acc ++ "!"
    case 0n PullHave{ev, cur, acc}:
      acc
    case 1n+p PullHave{ev, cur, acc}:
      pull.drain(p, PullNeed{cur, acc ++ pull.tag(ev)})
    case 0n PullNeed{cur, acc}:
      acc
    case 1n+p PullNeed{cur, acc}:
      pull.drain(p, pull.pack(acc, Pull.next(cur)))

# one JSON text as pull events
def pull.run(+src: String) -> String:
  pull.drain(pull.fuel(src), PullNeed{Pull.cursor(src), ""})

# the tag of the event after a whole-value skip
def pull.after.at(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  pull.tag(ev)

# the event after skipping the root value
def pull.after(src: String) -> String:
  pull.after.at(Pull.next(Pull.skip(Pull.cursor(src))))

# the event after the begin and one skipped element
def pull.elem.at(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  pull.after.at(Pull.next(Pull.skip(cur)))

# the second element of an array, the first having been skipped
def pull.elem(src: String) -> String:
  pull.elem.at(Pull.next(Pull.cursor(src)))

# key, then the value after it
def pull.tail.val(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  pull.tag(ev) ++ pull.after.at(Pull.next(cur))

# the second key, the first value having been skipped
def pull.tail.key(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  pull.tail.val(Pull.next(Pull.skip(cur)))

# past the first key
def pull.tail.mem(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  pull.tail.key(Pull.next(cur))

# the second key and its value, as tags. The first value is skipped
def pull.tail(src: String) -> String:
  pull.tail.mem(Pull.next(Pull.cursor(src)))

# whether the first string row is a span of the source or an owned copy
def pull.row.ev(ev: Pull.Ev) -> String:
  match ev:
    case Pull.EStrS{src, nn}:
      "span:" ++ Maybe.default(&2, String, Pull.text(ev), "")
    case Pull.EStr{body}:
      "own:" ++ body
    case other:
      "no"

# the event in hand
def pull.row.at(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  pull.row.ev(ev)

# the first element of the array
def pull.row3(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  pull.row.at(Pull.next(cur))

# the array after its key
def pull.row2(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  pull.row3(Pull.next(cur))

# the first key
def pull.row1(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  pull.row2(Pull.next(cur))

# the first string of {"rows":[...]}
def pull.row(src: String) -> String:
  pull.row1(Pull.next(Pull.cursor(src)))

# the first event, span or owned
def pull.own(src: String) -> String:
  pull.row.at(Pull.next(Pull.cursor(src)))

# text of the first event, or "none"
def pull.none.at(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  Maybe.default(&2, String, Pull.text(ev), "none")

# text of the first event, or "none"
def pull.none(src: String) -> String:
  pull.none.at(Pull.next(Pull.cursor(src)))

# "r" left times, comma-separated, with no trailing comma
def pull.rows(left: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n:
      "\"r\""
    case 1n+p:
      "\"r\"," ++ pull.rows(p)

# a weight-pack shaped object: a string-row array, then a small number
def pull.doc(left: Nat) -> String:
  "{\"rows\":[" ++ pull.rows(left) ++ "],\"n\":1}"

# 1, left times, comma-separated
def pull.numrow(left: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n:
      "1"
    case 1n+p:
      "1," ++ pull.numrow(p)

# an array of `1`, left times
def pull.nums(left: Nat) -> String:
  "[" ++ pull.numrow(left) ++ "]"

# one more for a string event when only strings count
def pull.add.str(ev: Pull.Ev, acc: U32) -> U32:
  match ev:
    case Pull.EStr{body}:
      U32.add(acc, 1)
    case Pull.EStrS{src, nn}:
      U32.add(acc, 1)
    case other:
      acc

# one more event, or one more string, depending on `only`
def pull.add(ev: Pull.Ev, acc: U32, only: Bool) -> U32:
  match only:
    case True{}:
      pull.add.str(ev, acc)
    case False{}:
      U32.add(acc, 1)

# the end event counts only when every event counts
def pull.finish(acc: U32, only: Bool) -> U32:
  match only:
    case True{}:
      acc
    case False{}:
      U32.add(acc, 1)

# the walk for a count: still need an event, or holding one
type PullCt is Data:
  CtNeed{cur: Pull.Cur, acc: U32}
  CtHave{ev: Pull.Ev, cur: Pull.Cur, acc: U32}

# an event just read, kept with the count so far
def pull.ct(acc: U32, got: (Pull.Ev & Pull.Cur)) -> PullCt:
  (ev, cur) = got
  CtHave{ev, cur, acc}

# count events until the end. `only` counts strings and ignores the rest
def pull.walk(left: Nat, ph: PullCt, +only: Bool) -> U32:
  match left ph:
    case n CtHave{Pull.EEnd{}, cur, acc}:
      pull.finish(acc, only)
    case n CtHave{Pull.EErr{}, cur, acc}:
      0
    case 0n CtHave{ev, cur, acc}:
      0
    case 1n+p CtHave{ev, cur, acc}:
      pull.walk(p, CtNeed{cur, pull.add(ev, acc, only)}, only)
    case 0n CtNeed{cur, acc}:
      0
    case 1n+p CtNeed{cur, acc}:
      pull.walk(p, pull.ct(acc, Pull.next(cur)), only)

# how many string values `next` yields. Not a parse tree
def pull.count(+src: String) -> U32:
  pull.walk(pull.fuel(src), CtNeed{Pull.cursor(src), 0}, True{})

# how many events `next` yields, including the end
def pull.events(+src: String) -> U32:
  pull.walk(pull.fuel(src), CtNeed{Pull.cursor(src), 0}, False{})

# the same walk as `pull.drain`, through the wrappers in main
def pull.pub.drain(left: Nat, ph: PullPh) -> String:
  match left ph:
    case n PullHave{Pull.EEnd{}, cur, acc}:
      acc ++ "."
    case n PullHave{Pull.EErr{}, cur, acc}:
      acc ++ "!"
    case 0n PullHave{ev, cur, acc}:
      acc
    case 1n+p PullHave{ev, cur, acc}:
      pull.pub.drain(p, PullNeed{cur, acc ++ pull.tag(ev)})
    case 0n PullNeed{cur, acc}:
      acc
    case 1n+p PullNeed{cur, acc}:
      pull.pub.drain(p, pull.pack(acc, Ezjson.next(cur)))

# one JSON text, read with the public cursor and next
def pull.pub(+src: String) -> String:
  pull.pub.drain(pull.fuel(src), PullNeed{Ezjson.cursor(src), ""})

# LAW: RFC 8259 §3 — pull reads null, true, and false as those events
law pull_atoms:
  {pull.run("null") ++ pull.run("true") ++ pull.run("false")
    == "null.true.false." : String}

# LAW: RFC 8259 §6 — pull keeps a number's spelling
law pull_nums:
  {pull.run("[0,-12,3.50,1e+2]") ++ pull.run("01") ++ pull.run("+1")
    ++ pull.run("NaN")
    == "[#0#-12#3.50#1e+2].!!!" : String}

# LAW: RFC 8259 §7 — a string with no escapes is a span; an escape is decoded
law pull_text:
  {pull.own("\"ab\"") ++ pull.own("\"a\\nb\"") ++ pull.own("\"\\u0041\"")
    ++ pull.run("\"\\uD800\\uDC00\"")
    == "span:abown:a\nbown:As:" ++ String.from_list([Char.from_u32(65536)]) ++ "." : String}

# LAW: RFC 8259 §2 — space, tab, line feed, and carriage return are not events
law pull_ws:
  {pull.run(" \t\r\n[ \t]\r\n") ++ pull.run("{ \n}") ++ pull.run("[\n1\r,\t2 ]")
    == "[].{}.[#1#2]." : String}

# LAW: RFC 8259 §2 and §4 — one value, and a trailing comma is rejected
law pull_one:
  {pull.run("1 2") ++ pull.run("") ++ pull.run("[1,]") ++ pull.run("{\"a\":1,}")
    ++ pull.run("] ")
    == "#1!![#1!{k:a#1!!" : String}

# LAW: RFC 8259 §7 and §8.1 — a raw control, a lone surrogate, and a BOM fail
law pull_bad:
  {pull.run("\"\n\"") ++ pull.run("\"\\uDEAD\"") ++ pull.run("\"\\uD800\"")
    ++ pull.run(String.from_list([Char.from_u32(65279)]) ++ "null")
    == "!!!!" : String}

# LAW: RFC 8259 §4 and §5 — objects and arrays, and a name is a decoded string
law pull_struct:
  {pull.run("[]") ++ pull.run("{}") ++ pull.run("[true,false]")
    ++ pull.run("{\"a\":1}") ++ pull.run("{\"a\\u0042\":3}")
    == "[].{}.[truefalse].{k:a#1}.{k:aB#3}." : String}

# LAW: skip drops one value. The next event is what followed it
law pull_skip:
  {pull.after("1") ++ pull.after("[1,2,3]") ++ pull.elem("[9,8]")
    ++ pull.tail("{\"a\":\"x\\ny\",\"b\":true}")
    == "..#8k:btrue" : String}

# LAW: a string row of a weight-pack object is a span, read one event at a time
law pull_span:
  {pull.row(pull.doc(4n)) == "span:r" : String}

# LAW: sixty-four string rows are sixty-four string events, not one parse tree
law pull_rows:
  {pull.count(pull.doc(64n)) == 64 : U32}

# LAW: skipping the row array still reaches the next key and its number
law pull_rows_skip:
  {pull.tail(pull.doc(64n)) == "k:n#1" : String}

# LAW: twenty-four numbers are twenty-seven events: begin, each, end, and done
law pull_steps:
  {pull.events(pull.nums(24n)) == 27 : U32}

# LAW: text copies a number and is none for null
law pull_copy:
  {pull.none("3.50") ++ pull.none("null") == "3.50none" : String}

# LAW: the public cursor and next agree with the pull cursor
law public_cursor:
  {pull.pub("null") == pull.run("null") : String}

# LAW: the public next reads an object the same way
law public_next:
  {pull.pub("{\"k\":true}") == "{k:ktrue}." : String}

# LAW: the public skip drops the same value the pull skip drops
law public_skip:
  {pull.after.at(Ezjson.next(Ezjson.skip(Ezjson.cursor("[1,2]"))))
    == pull.after.at(Pull.next(Pull.skip(Pull.cursor("[1,2]")))) : String}

# LAW: the public text copies a span the same way
law public_text:
  {Maybe.default(&2, String, Ezjson.text(Pull.EStrS{"ab", 2}), "")
    ++ Maybe.default(&2, String, Pull.text(Pull.ENum{"3.50", 4}), "")
    == "ab3.50" : String}
