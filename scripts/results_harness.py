"""Keep internal wrapper names out of interface model labels, preserving archives."""
import re


def display_harness_labels(value):
    if isinstance(value, list):
        return [display_harness_labels(item) for item in value]
    if isinstance(value, dict):
        return {key: (re.sub(r'\s*·\s*(?:tclaude|tcodex)\b(?:\s+v?\d[\w.-]*)?', '', item, flags=re.I)
                      if key == 'model_label' and isinstance(item, str)
                      else display_harness_labels(item)) for key, item in value.items()}
    return value
