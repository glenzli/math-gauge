"""Versioned, evaluator-side projection of candidate input identity surfaces.

This module does not rewrite source files, candidate answers, mathematical
statements or proof bodies.  Release export and import apply the same pure
projection before binding the resulting request and message hashes.
"""

import copy
import re


CANDIDATE_PROJECTION = "task-inputs.candidate-projection/v1"

_LEAN_NAMESPACE = re.compile(r"(?m)^([ \t]*(?:namespace|end)[ \t]+)MathGauge(?=\.)")
_CHAPTER_SCHEMA = re.compile(
    r'(?m)^([ \t]*"schema"[ \t]*:[ \t]*")math-gauge\.chapter-deliverables/v1(")'
)
_SOURCE_REPOSITORY_NOTICE = (
    "Public repository https://github.com/glenzli/oet-public at commit "
    "539b40cec73184d98e06d54fbd10e4b4698bd6e7. "
)
_EVALUATOR_STATUS_NOTICE = (
    " This is a draft task package; no generated solution has been evaluated or human-approved."
)


def project_candidate_text(name, content):
    """Return the v1 projection of one named candidate text attachment.

    Only the frozen input namespace delimiters, chapter-ledger schema and
    non-mathematical attribution wording change.  In particular LICENSE text
    and unknown attachment types are returned verbatim.  A new source identity
    surface requires an explicit projection-version change rather than a
    general URL or word scrubber.
    """
    if name.endswith(".lean"):
        return _LEAN_NAMESPACE.sub(r"\1TaskInputs", content)
    if name.rsplit("/", 1)[-1] == "obligations.json":
        return _CHAPTER_SCHEMA.sub(r"\1task-inputs.chapter-deliverables/v1\2", content)
    if name.rsplit("/", 1)[-1] == "ATTRIBUTION.md":
        return content.replace(_SOURCE_REPOSITORY_NOTICE, "").replace(
            "new Math Gauge benchmark design material", "new task design material"
        ).replace(_EVALUATOR_STATUS_NOTICE, "")
    return content


def project_candidate_request(request):
    """Copy a native request and project only its named visible input texts.

    Request metadata, task/instruction text and attachment names keep their
    original values; the native request schema is not the release wire schema.
    No inverse answer transform is provided: original candidate responses stay
    exact evidence even when they refer to the projected namespace.
    """
    projected = copy.deepcopy(request)
    for attachment in projected["files"]:
        attachment["content"] = project_candidate_text(attachment["name"], attachment["content"])
    return projected
