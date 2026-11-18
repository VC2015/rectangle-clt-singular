# Constructed nonsimple square-cone witness

This component checks the actual cone z >= |x| and z >= |y|. Four explicit
unit normals define four genuine facets, with strict point(0,0,1) and
explicit deletion witnesses. The origin has the complete active set of
four original facets and normal rank three. Its exact stratum is{0}, and
it is constructed as a native NonsimpleFaceIndex.

The square cone is a constructed verification witness motivated by the
arbitrary-edge discussion at supplement1081-1132. It is not a printed
assertion, does not add a manuscript statement or proof-environment count,
and does not certify the missing literal nonsimple ridge Green identity.

The checkpoint performs a Lake target build, forced direct source replay,
strict29-target transitive axiom audit, and full29-type/project-graph export.
Only propext, Classical.choice and Quot.sound are allowed. The source and
the exact fixture/command logs are hash-bound in checkpoint-1/run.json.

To reproduce without overwriting the immutable checkpoint, use a fresh
output directory and the same frozen source with its pinned dependencies:

```sh
python3 evidence/supplemental-h-nonsimple-square/checkpoint-1/run.py \
  --root "$PWD" --output /tmp/nonsimple-square-fresh-checkpoint
```

The runner refuses an existing run.json and verifies source identity before
and after all four commands. Independent review is recorded separately.
