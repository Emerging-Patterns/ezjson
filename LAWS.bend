# ezjson's laws. Each guarantee is one file under laws/, its prose on top and
# its quantified laws under it, proved by the file of the same name under
# proofs/; LAWS.bend and PROOF.bend only import them. The gate: the first line
# `bend PROOF.bend` prints is exactly `ALL PROOFS CHECK`. Tests and fixtures
# are never evidence for a guarantee; what ezjson cannot prove is said where
# it is assumed, on the code.
#
# There are two families: conformance to RFC 8259 (the text, number, string
# and print guarantees) and the public interface in main.bend (the tree, the
# pull cursor and fixed decimals). Every other module is internal and carries
# no promise.
#
# A value is well-formed when `V.wf` holds of it: its arrays and objects are
# chains of cells ending in `JNil`, no cell stands where a value belongs, and
# every number's text is a JSON number. Every value built through `main.bend`
# or returned by `parse` is well-formed (laws/BuiltValuesWellFormed.bend).
# `same` is the specification relation "the same JSON value", which ignores
# whether a string or key is owned or a span of the source. `LAWS.bend`
# decides it with `own`, which reads every span out into its own string: two
# values are `same` when their `own` forms are equal.
#
# The number rule of RFC 8259 §6 is written out as `number` and the defs above
# it in laws/defs/CursorAndNumberRules.bend, one def per ABNF production, so
# laws/NumOkIsNumberRule.bend can be checked against the RFC by reading those
# defs.
#
# The reasoning behind each guarantee is in docs/rfc/ezjson-spec.md, and every
# law as it stood then in docs/rfc/ezjson-law-inventory.md. They name the
# guarantees by the requirement IDs of docs/SPEC.md, the table these files
# replaced.
import Base
import ./laws/AsF32ReadsFiniteFloats.bend as AsF32ReadsFiniteFloats
import ./laws/AsU32ReadsPlainDigits.bend as AsU32ReadsPlainDigits
import ./laws/AtIndexesArrays.bend as AtIndexesArrays
import ./laws/BareWordsAreLiteralsOrNumbers.bend as BareWordsAreLiteralsOrNumbers
import ./laws/BuiltValuesWellFormed.bend as BuiltValuesWellFormed
import ./laws/ByteOrderMarkRefused.bend as ByteOrderMarkRefused
import ./laws/CursorEndSticks.bend as CursorEndSticks
import ./laws/CursorErrorSticks.bend as CursorErrorSticks
import ./laws/CursorEventsMatchParse.bend as CursorEventsMatchParse
import ./laws/EscapesDecode.bend as EscapesDecode
import ./laws/EventTextReadsStrings.bend as EventTextReadsStrings
import ./laws/FixedKeepsMinus.bend as FixedKeepsMinus
import ./laws/FixedRoundsHalfToEven.bend as FixedRoundsHalfToEven
import ./laws/FixedSplitsMantissaAndExponent.bend as FixedSplitsMantissaAndExponent
import ./laws/FixedWritesDigits.bend as FixedWritesDigits
import ./laws/FixedWritesValidNumbers.bend as FixedWritesValidNumbers
import ./laws/GetFindsFirstKey.bend as GetFindsFirstKey
import ./laws/HasFindsKey.bend as HasFindsKey
import ./laws/IsArrIsObjTellKinds.bend as IsArrIsObjTellKinds
import ./laws/ItemsGivesElements.bend as ItemsGivesElements
import ./laws/LenCountsItems.bend as LenCountsItems
import ./laws/NamesCompareDecoded.bend as NamesCompareDecoded
import ./laws/NumBuildsOrNull.bend as NumBuildsOrNull
import ./laws/NumOkIsNumberRule.bend as NumOkIsNumberRule
import ./laws/NumberKeepsSpelling.bend as NumberKeepsSpelling
import ./laws/ParsesExactlyJsonTexts.bend as ParsesExactlyJsonTexts
import ./laws/PrettyRoundTrips.bend as PrettyRoundTrips
import ./laws/PrintIsCompactAndStable.bend as PrintIsCompactAndStable
import ./laws/PrintRoundTrips.bend as PrintRoundTrips
import ./laws/PullFailedSkip.bend as PullFailedSkip
import ./laws/QuoteEscapesExactly.bend as QuoteEscapesExactly
import ./laws/QuotedStringReadsBack.bend as QuotedStringReadsBack
import ./laws/RawControlCharsRefused.bend as RawControlCharsRefused
import ./laws/ReadersReadBuilders.bend as ReadersReadBuilders
import ./laws/ReadersRefuseOtherKinds.bend as ReadersRefuseOtherKinds
import ./laws/SkipFailsWhereNoValue.bend as SkipFailsWhereNoValue
import ./laws/SkipPassesOneValue.bend as SkipPassesOneValue
import ./laws/SpansReadAsOwned.bend as SpansReadAsOwned
import ./laws/TextHoldsOneValue.bend as TextHoldsOneValue
import ./laws/WhitespaceBetweenTokensIgnored.bend as WhitespaceBetweenTokensIgnored
