# ezjson: the laws. Closed equalities from parse/print/query; PROOF.bend fills them.
import Base
import ./value.bend as V
import ./lex.bend as Lex
import ./parse.bend as Parse
import ./print.bend as Print
import ./lazy.bend as Lazy
import ./main.bend as Ezjson

# parse then print; a failure is "<bad>"
def again(text: String) -> String:
  Print.maybe(Parse.parse(text))

# a built JSON message
def msg() -> V.Json:
  V.obj([("id", V.num(7)), ("method", V.JStr{"open"}),
    ("params", V.obj([("uri", V.JStr{"file:///a.bend"}),
      ("tags", V.arr([V.JNull{}, V.JBool{True{}}]))]))])

# a parse result or JNull
def parsed(m: Maybe<&2, V.Json>) -> V.Json:
  Maybe.default(&2, V.Json, m, V.JNull{})

# LAW: null round-trips
law roundtrip_null:
  {again("null") == "null" : String}

# LAW: booleans round-trip
law roundtrip_bools:
  {again("[true,false]") == "[true,false]" : String}

# LAW: numbers keep their text
law roundtrip_nums:
  {again("[0,-12,3.50,1e9]") == "[0,-12,3.50,1e9]" : String}

# LAW: whitespace goes
law roundtrip_space:
  {again(" { \"a\" : [ 1 , 2 ] ,\n\t\"b\" : { } } ") == "{\"a\":[1,2],\"b\":{}}" : String}

# LAW: escapes print decoded
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

# LAW: two roots are bad
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
  {V.str_or(V.get(V.get(msg(), "params"), "uri"), "?") == "file:///a.bend" : String}

# LAW: a number reads
law get_id:
  {V.u32_or(V.get(msg(), "id"), 0) == 7 : U32}

# LAW: a missing key reads the default
law get_missing:
  {V.str_or(V.get(V.get(msg(), "nope"), "uri"), "?") == "?" : String}

# LAW: a string is not a number
law get_not_num:
  {V.u32_or(V.get(msg(), "method"), 99) == 99 : U32}

# LAW: parsed text at a is an object, not a string
law parse_obj_not_str:
  {V.str_or(V.get(parsed(Parse.parse("{\"a\":{\"b\":\"deep\"}}")), "a"), "?") == "?" : String}

# LAW: parsed paths chain
law parse_path_chain:
  {V.str_or(V.get(V.get(parsed(Parse.parse("{\"a\":{\"b\":\"deep\"}}")), "a"), "b"), "?")
    == "deep" : String}

# LAW: an array's first item
law arr_first:
  {Print.print(V.first(V.arr([V.JNull{}, V.num(1)]))) == "null" : String}

# LAW: find on a missing key is JNull
law find_missing:
  {V.str_or(V.find(V.JNil{}, "k"), "?") == "?" : String}

# LAW: reverse of no cells is the acc
law reverse_nil:
  {Print.print(V.reverse(V.JNil{}, V.JNull{})) == "null" : String}

# LAW: a quoted string
law print_quote:
  {Print.quote("a") == "\"a\"" : String}

# LAW: escape of a quote
law print_escape:
  {Print.escape(['"']) == "\\\"" : String}

# LAW: a bare null word
law parse_word_null:
  {Print.print(Parse.word("null")) == "null" : String}

# LAW: a bare true word
law parse_word_true:
  {Print.print(Parse.word("true")) == "true" : String}

# LAW: a bare false word
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

# LAW: an empty object prints
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

# LAW: the public arr
law public_arr:
  {Ezjson.print(Ezjson.arr([])) == "[]" : String}

# LAW: the public num
law public_num:
  {Ezjson.print(Ezjson.num(7)) == "7" : String}

# LAW: the public get
law public_get:
  {V.str_or(Ezjson.get(Ezjson.obj([("k", V.JStr{"v"})]), "k"), "?") == "v" : String}

# LAW: the public str_or
law public_str_or:
  {Ezjson.str_or(V.JStr{"a"}, "?") == "a" : String}

# LAW: the public u32_or
law public_u32_or:
  {Ezjson.u32_or(V.JNum{"7"}, 0) == 7 : U32}

# LAW: a missing comma, a trailing comma, a missing colon, and a trailing root
# comma are not JSON
law parse_seps:
  {again("[1,2]") ++ again("[1 2]") ++ again("[1,]") ++ again("{\"a\":1}")
    ++ again("{\"a\" 1}") ++ again("{\"a\":1,}") ++ again("1,")
    == "[1,2]<bad><bad>{\"a\":1}<bad><bad><bad>" : String}

# LAW: a number keeps its spelling, and a non-number word is bad
law parse_number:
  {again("[-0,1e+2,3.50]") ++ again("01") ++ again("-") ++ again("1.") ++ again("+1")
    == "[-0,1e+2,3.50]<bad><bad><bad><bad>" : String}

# LAW: a bad escape, a short \\u, and a raw control are bad
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

# LAW: a surrogate pair is one code point
law parse_surrogate:
  {code(V.str_or(parsed(Parse.parse("\"\\uD800\\uDC00\"")), "")) == 65536 : U32}

# LAW: the public null
law public_null:
  {Ezjson.print(Ezjson.null()) == Print.print(V.null()) : String}

# LAW: the public bool
law public_bool:
  {Ezjson.print(Ezjson.bool(False{})) == Print.print(V.bool(False{})) : String}

# LAW: the public str
law public_str:
  {Ezjson.str_or(Ezjson.str("a"), "?") == V.str_or(V.str("a"), "?") : String}

# LAW: the public neg; zero stays zero
law public_neg:
  {Ezjson.print(Ezjson.neg(2)) ++ Print.print(V.neg(0)) == "-2" ++ "0" : String}

# LAW: the public f32 is the value f32
law public_f32:
  {Ezjson.print(Ezjson.f32((1.5 : F32))) == Print.print(V.f32((1.5 : F32))) : String}

# LAW: the public number keeps a JSON number and drops any other text
law public_number:
  {Ezjson.print(Ezjson.number("3.50")) ++ Print.print(V.number("01")) == "3.50null" : String}

# LAW: the public at
law public_at:
  {Ezjson.str_or(Ezjson.at(Ezjson.arr([Ezjson.str("z")]), 0), "?")
    == V.str_or(V.at(V.arr([V.str("z")]), 0), "?") : String}

# LAW: the public bool_or
law public_bool_or:
  {Ezjson.bool_or(Ezjson.bool(True{}), False{}) == V.bool_or(V.bool(True{}), False{}) : Bool}

# LAW: the public f32_or
law public_f32_or:
  {F32.show(Ezjson.f32_or(Ezjson.num(2), (0.0 : F32)))
    == F32.show(V.f32_or(V.num(2), (0.0 : F32))) : String}
