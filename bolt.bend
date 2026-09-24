# bolt.bend: how bolt lints this repo. Every rule is an error except
# `coverage`, which warns until the laws exist: the gate must see no errors.
# See bolt/config.bend for the groups and levels.
import Base

# what will fail or blow up
def correctness() -> String:
  "error"

# what is probably a slip
def suspicious() -> String:
  "error"

# comments and whitespace
def style() -> String:
  "error"

# a def named by no quantified law: advice while SPEC.md's requirements are
# pending, since deleting the closed laws left defs no law names. That rule
# is `coverage` (L001).
def laws() -> String:
  "warn"

# a law with no binder
def closed() -> String:
  "error"

# an @unsafe def a law file reaches
def unsafe() -> String:
  "error"

# SPEC.md's rows and the laws' tags agree
def trace() -> String:
  "error"
