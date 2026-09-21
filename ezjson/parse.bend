# ezjson/parse: tokens to a value, one token per step, over an explicit stack of
# open arrays and objects: a loop, with no fuel and no recursion on the value.
# Lenient about commas and colons; strict about nesting and a single root.
import Base
import ./value.bend as V
import ./lex.bend as Lex

# an open array (its items, reversed) or an open object (its pairs, reversed,
# and the key awaiting its value)
type Frame is Data:
  FArr{items: V.Json}
  FObj{pairs: V.Json, key: Maybe<&2, String>}

# the parser's state: an error was seen, the finished root, the open frames
type P is Data:
  P{bad: Bool, root: Maybe<&2, V.Json>, stack: List<&2, Frame>}

# a bare word as a value: null, true, false, else a number kept as text
def word(+raw: String) -> V.Json:
  Bool.pick(V.Json, String.eq(raw, "null"), V.JNull{},
    Bool.pick(V.Json, String.eq(raw, "true"), V.JBool{True{}},
      Bool.pick(V.Json, String.eq(raw, "false"), V.JBool{False{}}, V.JNum{raw})))

# a finished value lands in the innermost open frame, or becomes the root
def put(stack: List<&2, Frame>, root: Maybe<&2, V.Json>, v: V.Json, bad: Bool) -> P:
  match stack root v:
    case Nil{} None{} val:
      P{bad, Some{val}, Nil{}}
    case Nil{} Some{r} val:
      P{True{}, Some{r}, Nil{}}
    case Con{FArr{items}, rest} r val:
      P{bad, r, FArr{V.JCons{val, items}} <> rest}
    case Con{FObj{pairs, None{}}, rest} r V.JStr{k}:
      P{bad, r, FObj{pairs, Some{k}} <> rest}
    case Con{FObj{pairs, None{}}, rest} r val:
      P{True{}, r, rest}
    case Con{FObj{pairs, Some{k}}, rest} r val:
      P{bad, r, FObj{V.JPair{k, val, pairs}, None{}} <> rest}

# a `]`: the innermost frame must be an array
def close_arr(stack: List<&2, Frame>, root: Maybe<&2, V.Json>, bad: Bool) -> P:
  match stack:
    case Con{FArr{items}, rest}:
      put(rest, root, V.JArr{V.reverse(items, V.JNil{})}, bad)
    case other:
      P{True{}, root, Nil{}}

# a `}`: the innermost frame must be an object with no key waiting
def close_obj(stack: List<&2, Frame>, root: Maybe<&2, V.Json>, bad: Bool) -> P:
  match stack:
    case Con{FObj{pairs, None{}}, rest}:
      put(rest, root, V.JObj{V.reverse(pairs, V.JNil{})}, bad)
    case other:
      P{True{}, root, Nil{}}

# one token
def step(tok: Lex.Tok, st: P) -> P:
  match tok:
    case Lex.TOpenArr{}:
      P{bad, root, stack} = st
      P{bad, root, FArr{V.JNil{}} <> stack}
    case Lex.TOpenObj{}:
      P{bad, root, stack} = st
      P{bad, root, FObj{V.JNil{}, None{}} <> stack}
    case Lex.TCloseArr{}:
      P{bad, root, stack} = st
      close_arr(stack, root, bad)
    case Lex.TCloseObj{}:
      P{bad, root, stack} = st
      close_obj(stack, root, bad)
    case Lex.TColon{}:
      st
    case Lex.TComma{}:
      st
    case Lex.TStr{s}:
      P{bad, root, stack} = st
      put(stack, root, V.JStr{s}, bad)
    case Lex.TWord{raw}:
      P{bad, root, stack} = st
      put(stack, root, word(raw), bad)
    case Lex.TBad{}:
      P{bad, root, stack} = st
      P{True{}, root, stack}

# every token, in order
def run(toks: List<&2, Lex.Tok>, st: P) -> P:
  match toks:
    case Nil{}:
      st
    case Con{t, rest}:
      run(rest, step(t, st))

# the root, when nothing went wrong and nothing stayed open
def result(bad: Bool, stack: List<&2, Frame>, root: Maybe<&2, V.Json>) -> Maybe<&2, V.Json>:
  match bad stack root:
    case False{} Nil{} Some{j}:
      Some{j}
    case b s r:
      None{}

# the value once the tokens are over
def finish(st: P) -> Maybe<&2, V.Json>:
  P{bad, root, stack} = st
  result(bad, stack, root)

# a text as a value, or None when it is not JSON
def parse(s: String) -> Maybe<&2, V.Json>:
  finish(run(Lex.tokens(s), P{False{}, None{}, Nil{}}))
