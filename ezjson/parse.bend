# ezjson/parse: tokens to one JSON value. Commas separate elements, a colon
# separates a key from its value, and a text has one root.
import Base
import ./value.bend as V
import ./lex.bend as Lex

# where the next token of an open array or object has to be
type Slot is Data:
  SValue{}
  SComma{}
  SKey{}
  SColon{}

# an object key: owned text, or the first `n` chars of a source suffix
type Key is Data:
  KOwn{s: String}
  KCut{src: String, n: U32}

# an open array (its items, reversed) or an open object (its pairs, reversed,
# and the key awaiting its value)
type Frame is Data:
  FArr{items: V.Json, slot: Slot}
  FObj{pairs: V.Json, key: Key, slot: Slot}

# the parser's state: an error was seen, the finished root, the open frames
type P is Data:
  P{bad: Bool, root: Maybe<&2, V.Json>, stack: List<&2, Frame>}

def word.ok(+raw: String) -> Bool:
  Bool.or(String.eq(raw, "null"),
    Bool.or(String.eq(raw, "true"),
      Bool.or(String.eq(raw, "false"), V.num.ok(raw))))

# a bare word as a value: null, true, false, else a number kept as text
def word(+raw: String) -> V.Json:
  Bool.pick(V.Json, String.eq(raw, "null"), V.JNull{},
    Bool.pick(V.Json, String.eq(raw, "true"), V.JBool{True{}},
      Bool.pick(V.Json, String.eq(raw, "false"), V.JBool{False{}}, V.JNum{raw})))

def step.ready(stack: List<&2, Frame>, root: Maybe<&2, V.Json>) -> Bool:
  match stack root:
    case Nil{} None{}:
      True{}
    case Con{FArr{items, SValue{}}, rest} r:
      True{}
    case Con{FObj{pairs, key, SValue{}}, rest} r:
      True{}
    case s r:
      False{}

def put.pair(key: Key, val: V.Json, pairs: V.Json) -> V.Json:
  match key:
    case KOwn{s}:
      V.JPair{s, val, pairs}
    case KCut{src, n}:
      V.JBind{src, n, val, pairs}

def put.text(key: Key) -> V.Json:
  match key:
    case KOwn{s}:
      V.JStr{s}
    case KCut{src, n}:
      V.JSpan{src, n}

# a finished value lands in the innermost open frame, or becomes the root
def put(stack: List<&2, Frame>, root: Maybe<&2, V.Json>, v: V.Json, bad: Bool) -> P:
  match stack root v:
    case Nil{} None{} val:
      P{bad, Some{val}, Nil{}}
    case Nil{} Some{r} val:
      P{True{}, Some{r}, Nil{}}
    case Con{FArr{items, SValue{}}, rest} r val:
      P{bad, r, FArr{V.JCons{val, items}, SComma{}} <> rest}
    case Con{FObj{pairs, k, SValue{}}, rest} r val:
      P{bad, r, FObj{put.pair(k, val, pairs), KOwn{""}, SComma{}} <> rest}
    case s r val:
      P{True{}, r, Nil{}}

def put.str(stack: List<&2, Frame>, root: Maybe<&2, V.Json>, key: Key, bad: Bool) -> P:
  match stack:
    case Con{FObj{pairs, k, SKey{}}, rest}:
      P{bad, root, FObj{pairs, key, SColon{}} <> rest}
    case other:
      put(stack, root, put.text(key), bad)

def step.open_arr.go(bad: Bool, root: Maybe<&2, V.Json>, stack: List<&2, Frame>, ok: Bool) -> P:
  match ok:
    case True{}:
      P{bad, root, FArr{V.JNil{}, SValue{}} <> stack}
    case False{}:
      P{True{}, root, Nil{}}

def step.open_arr(st: P) -> P:
  P{bad, +root, +stack} = st
  step.open_arr.go(bad, root, stack, step.ready(stack, root))

def step.open_obj.go(bad: Bool, root: Maybe<&2, V.Json>, stack: List<&2, Frame>, ok: Bool) -> P:
  match ok:
    case True{}:
      P{bad, root, FObj{V.JNil{}, KOwn{""}, SKey{}} <> stack}
    case False{}:
      P{True{}, root, Nil{}}

def step.open_obj(st: P) -> P:
  P{bad, +root, +stack} = st
  step.open_obj.go(bad, root, stack, step.ready(stack, root))

def step.comma(stack: List<&2, Frame>, root: Maybe<&2, V.Json>, bad: Bool) -> P:
  match stack:
    case Con{FArr{items, SComma{}}, rest}:
      P{bad, root, FArr{items, SValue{}} <> rest}
    case Con{FObj{pairs, k, SComma{}}, rest}:
      P{bad, root, FObj{pairs, KOwn{""}, SKey{}} <> rest}
    case other:
      P{True{}, root, Nil{}}

def step.colon(stack: List<&2, Frame>, root: Maybe<&2, V.Json>, bad: Bool) -> P:
  match stack:
    case Con{FObj{pairs, k, SColon{}}, rest}:
      P{bad, root, FObj{pairs, k, SValue{}} <> rest}
    case other:
      P{True{}, root, Nil{}}

def step.word.go(raw: String, st: P, ok: Bool) -> P:
  P{bad, root, stack} = st
  match ok:
    case True{}:
      put(stack, root, word(raw), bad)
    case False{}:
      P{True{}, root, stack}

def step.word(+raw: String, st: P) -> P:
  step.word.go(raw, st, word.ok(raw))

# a `]`: the innermost frame must be an array, empty or just after a value
def close_arr(stack: List<&2, Frame>, root: Maybe<&2, V.Json>, bad: Bool) -> P:
  match stack:
    case Con{FArr{V.JNil{}, SValue{}}, rest}:
      put(rest, root, V.JArr{V.JNil{}}, bad)
    case Con{FArr{items, SComma{}}, rest}:
      put(rest, root, V.JArr{V.reverse(items, V.JNil{})}, bad)
    case other:
      P{True{}, root, Nil{}}

# a `}`: the innermost frame must be an object, empty or just after a value
def close_obj(stack: List<&2, Frame>, root: Maybe<&2, V.Json>, bad: Bool) -> P:
  match stack:
    case Con{FObj{V.JNil{}, k, SKey{}}, rest}:
      put(rest, root, V.JObj{V.JNil{}}, bad)
    case Con{FObj{pairs, k, SComma{}}, rest}:
      put(rest, root, V.JObj{V.reverse(pairs, V.JNil{})}, bad)
    case other:
      P{True{}, root, Nil{}}

def step.span.ok(+raw: String, ok: Bool) -> (V.Json & Bool):
  match ok:
    case True{}:
      (V.JNum{raw}, True{})
    case False{}:
      (V.JNull{}, False{})

def step.span.use(+raw: String) -> (V.Json & Bool):
  step.span.ok(raw, V.num.ok(raw))

def step.span.chk(src: String, +n: U32) -> (V.Json & Bool):
  step.span.use(V.span.str(src, n, U32.is_zero(n)))

def step.span.go(src: String, n: U32, a: Bool, b: Bool, c: Bool) -> (V.Json & Bool):
  match a b c:
    case True{} x y:
      (V.JNull{}, True{})
    case False{} True{} y:
      (V.JBool{True{}}, True{})
    case False{} False{} True{}:
      (V.JBool{False{}}, True{})
    case False{} False{} False{}:
      step.span.chk(src, n)

def step.span.use2(st: P, v: V.Json, ok: Bool) -> P:
  P{bad, root, stack} = st
  match ok:
    case True{}:
      put(stack, root, v, bad)
    case False{}:
      P{True{}, root, stack}

def step.span.open(st: P, got: (V.Json & Bool)) -> P:
  (v, ok) = got
  step.span.use2(st, v, ok)

def step.span(+src: String, +n: U32, st: P) -> P:
  step.span.open(st, step.span.go(src, n, V.span.eq(src, n, "null"),
    V.span.eq(src, n, "true"), V.span.eq(src, n, "false")))

# one token
def step(tok: Lex.Tok, st: P) -> P:
  match tok:
    case Lex.TOpenArr{}:
      step.open_arr(st)
    case Lex.TOpenObj{}:
      step.open_obj(st)
    case Lex.TCloseArr{}:
      P{bad, root, stack} = st
      close_arr(stack, root, bad)
    case Lex.TCloseObj{}:
      P{bad, root, stack} = st
      close_obj(stack, root, bad)
    case Lex.TColon{}:
      P{bad, root, stack} = st
      step.colon(stack, root, bad)
    case Lex.TComma{}:
      P{bad, root, stack} = st
      step.comma(stack, root, bad)
    case Lex.TStr{s}:
      P{bad, root, stack} = st
      put.str(stack, root, KOwn{s}, bad)
    case Lex.TWord{raw}:
      step.word(raw, st)
    case Lex.TStrS{src, n}:
      P{bad, root, stack} = st
      put.str(stack, root, KCut{src, n}, bad)
    case Lex.TWordS{src, n}:
      step.span(src, n, st)
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
