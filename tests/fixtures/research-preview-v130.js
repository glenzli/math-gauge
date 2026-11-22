globalThis.MGResearchPreviewData = {
  "schema": "math-gauge.research-board-preview/v1",
  "edition": "1.3.0",
  "kind": "synthetic-fixture",
  "category": {
    "id": "open-research",
    "zh": "独立开放研究",
    "en": "Independent Open Research"
  },
  "rank_eligible": false,
  "default_order": "retained-base-SMC",
  "weights_ratified": false,
  "rows": [
    {
      "id": "fixture-alpha",
      "label": "示例 A",
      "kind": "synthetic-fixture",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 85,
      "components": {
        "autonomy": {
          "state": "reviewed",
          "value": 45,
          "strict": true
        },
        "taste": {
          "state": "reviewed",
          "value": 65,
          "strict": true
        },
        "capacity": {
          "state": "reviewed",
          "value": 80,
          "strict": true
        }
      },
      "task_strict": 100,
      "item": {
        "lower": 67.5,
        "upper": 67.5,
        "exact": 67.5
      },
      "coverage": {
        "planned": 1,
        "reviewed": 1,
        "components_planned": 3,
        "components_reviewed": 3
      },
      "strict_overall": {
        "lower": 86.5,
        "upper": 86.5,
        "exact": 86.5
      },
      "composites": {
        "MC": {
          "lower": 83.25,
          "upper": 83.25,
          "exact": 83.25
        },
        "RMC": {
          "lower": 83.25,
          "upper": 83.25,
          "exact": 83.25
        },
        "SMC": {
          "lower": 83.25,
          "upper": 83.25,
          "exact": 83.25
        }
      },
      "confirmed": {
        "MC": 83.25,
        "RMC": 83.25,
        "SMC": 83.25
      },
      "strict_confirmed": 86.5,
      "composite": {
        "lower": 83.25,
        "upper": 83.25,
        "exact": 83.25
      }
    },
    {
      "id": "fixture-beta",
      "label": "示例 B",
      "kind": "synthetic-fixture",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 75,
      "components": {
        "autonomy": {
          "state": "reviewed",
          "value": 0,
          "strict": false
        },
        "taste": {
          "state": "reviewed",
          "value": 40,
          "strict": false
        },
        "capacity": {
          "state": "reviewed",
          "value": 20,
          "strict": false
        }
      },
      "task_strict": 0,
      "item": {
        "lower": 20.0,
        "upper": 20.0,
        "exact": 20.0
      },
      "coverage": {
        "planned": 1,
        "reviewed": 1,
        "components_planned": 3,
        "components_reviewed": 3
      },
      "strict_overall": {
        "lower": 67.5,
        "upper": 67.5,
        "exact": 67.5
      },
      "composites": {
        "MC": {
          "lower": 69.5,
          "upper": 69.5,
          "exact": 69.5
        },
        "RMC": {
          "lower": 69.5,
          "upper": 69.5,
          "exact": 69.5
        },
        "SMC": {
          "lower": 69.5,
          "upper": 69.5,
          "exact": 69.5
        }
      },
      "confirmed": {
        "MC": 69.5,
        "RMC": 69.5,
        "SMC": 69.5
      },
      "strict_confirmed": 67.5,
      "composite": {
        "lower": 69.5,
        "upper": 69.5,
        "exact": 69.5
      }
    },
    {
      "id": "fixture-gamma",
      "label": "示例 C",
      "kind": "synthetic-fixture",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 65,
      "components": {
        "autonomy": {
          "state": "reviewed",
          "value": 70,
          "strict": true
        },
        "taste": {
          "state": "insufficient-evidence",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "reviewed",
          "value": 60,
          "strict": false
        }
      },
      "task_strict": 0,
      "item": {
        "lower": 47.5,
        "upper": 72.5,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 2
      },
      "strict_overall": {
        "lower": 58.5,
        "upper": 58.5,
        "exact": 58.5
      },
      "composites": {
        "MC": {
          "lower": 63.25,
          "upper": 65.75,
          "exact": null
        },
        "RMC": {
          "lower": 63.25,
          "upper": 65.75,
          "exact": null
        },
        "SMC": {
          "lower": 63.25,
          "upper": 65.75,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 63.25,
        "RMC": 63.25,
        "SMC": 63.25
      },
      "strict_confirmed": 58.5,
      "composite": {
        "lower": 63.25,
        "upper": 65.75,
        "exact": null
      }
    },
    {
      "id": "fixture-delta",
      "label": "示例 D",
      "kind": "synthetic-fixture",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 55,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 49.5,
        "upper": 59.5,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 49.5,
          "upper": 59.5,
          "exact": null
        },
        "RMC": {
          "lower": 49.5,
          "upper": 59.5,
          "exact": null
        },
        "SMC": {
          "lower": 49.5,
          "upper": 59.5,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 49.5,
        "RMC": 49.5,
        "SMC": 49.5
      },
      "strict_confirmed": 49.5,
      "composite": {
        "lower": 49.5,
        "upper": 59.5,
        "exact": null
      }
    },
    {
      "id": "fixture-epsilon",
      "label": "示例 E",
      "kind": "synthetic-fixture",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 45,
      "components": {
        "autonomy": {
          "state": "unreviewed",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "unreviewed",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "unreviewed",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 40.5,
        "upper": 50.5,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 40.5,
          "upper": 50.5,
          "exact": null
        },
        "RMC": {
          "lower": 40.5,
          "upper": 50.5,
          "exact": null
        },
        "SMC": {
          "lower": 40.5,
          "upper": 50.5,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 40.5,
        "RMC": 40.5,
        "SMC": 40.5
      },
      "strict_confirmed": 40.5,
      "composite": {
        "lower": 40.5,
        "upper": 50.5,
        "exact": null
      }
    }
  ]
};
globalThis.MGResearchBaselineData = {
  "schema": "math-gauge.research-board-preview/v1",
  "edition": "1.3.0",
  "kind": "existing-model-unmeasured",
  "category": {
    "id": "open-research",
    "zh": "独立开放研究",
    "en": "Independent Open Research"
  },
  "rank_eligible": false,
  "default_order": "retained-base-SMC",
  "weights_ratified": false,
  "source_binding": {
    "edition": "1.2.0",
    "sha256": "bfaa10cb07423b46d89f030a2a5622787ad5028c1fe18898a5949f16d2961571"
  },
  "rows": [
    {
      "id": "astra-6-max",
      "label": "Astra 6 (max)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 91.33333333333333,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 81.61904761904762,
        "upper": 91.61904761904762,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 85.02539682539683,
          "upper": 95.02539682539683,
          "exact": null
        },
        "RMC": {
          "lower": 85.02539682539683,
          "upper": 95.02539682539683,
          "exact": null
        },
        "SMC": {
          "lower": 81.61904761904762,
          "upper": 91.61904761904762,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 85.02539682539683,
        "RMC": 85.02539682539683,
        "SMC": 81.61904761904762
      },
      "strict_confirmed": 81.61904761904762,
      "composite": {
        "lower": 85.02539682539683,
        "upper": 95.02539682539683,
        "exact": null
      }
    },
    {
      "id": "sol-6.1-max",
      "label": "Sol 6.1 (max)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 91.33333333333333,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 81.61904761904762,
        "upper": 91.61904761904762,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 85.02539682539683,
          "upper": 95.02539682539683,
          "exact": null
        },
        "RMC": {
          "lower": 84.94539682539683,
          "upper": 94.94539682539683,
          "exact": null
        },
        "SMC": {
          "lower": 81.61904761904762,
          "upper": 91.61904761904762,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 85.02539682539683,
        "RMC": 84.94539682539683,
        "SMC": 81.61904761904762
      },
      "strict_confirmed": 81.61904761904762,
      "composite": {
        "lower": 84.94539682539683,
        "upper": 94.94539682539683,
        "exact": null
      }
    },
    {
      "id": "sol-6.2-max",
      "label": "Sol 6.2 (max)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 91.33333333333333,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 81.61904761904762,
        "upper": 91.61904761904762,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 84.58095238095238,
          "upper": 94.58095238095238,
          "exact": null
        },
        "RMC": {
          "lower": 84.58095238095238,
          "upper": 94.58095238095238,
          "exact": null
        },
        "SMC": {
          "lower": 81.61904761904762,
          "upper": 91.61904761904762,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 84.58095238095238,
        "RMC": 84.58095238095238,
        "SMC": 81.61904761904762
      },
      "strict_confirmed": 81.61904761904762,
      "composite": {
        "lower": 84.58095238095238,
        "upper": 94.58095238095238,
        "exact": null
      }
    },
    {
      "id": "astra-6.2-max",
      "label": "Astra 6.2 (max)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 89.73333333333333,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 80.01904761904763,
        "upper": 90.01904761904763,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 84.26095238095238,
          "upper": 94.26095238095238,
          "exact": null
        },
        "RMC": {
          "lower": 84.26095238095238,
          "upper": 94.26095238095238,
          "exact": null
        },
        "SMC": {
          "lower": 80.01904761904763,
          "upper": 90.01904761904763,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 84.26095238095238,
        "RMC": 84.26095238095238,
        "SMC": 80.01904761904763
      },
      "strict_confirmed": 80.01904761904763,
      "composite": {
        "lower": 84.26095238095238,
        "upper": 94.26095238095238,
        "exact": null
      }
    },
    {
      "id": "astra-6.2-xhigh",
      "label": "Astra 6.2 (xHigh)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 85.23333333333333,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 75.87619047617761,
        "upper": 85.87619047617761,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 84.04666666666238,
          "upper": 94.04666666666238,
          "exact": null
        },
        "RMC": {
          "lower": 83.04666666666238,
          "upper": 93.04666666666238,
          "exact": null
        },
        "SMC": {
          "lower": 75.87619047617761,
          "upper": 85.87619047617761,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 84.04666666666238,
        "RMC": 83.04666666666238,
        "SMC": 75.87619047617761
      },
      "strict_confirmed": 75.87619047617761,
      "composite": {
        "lower": 83.04666666666238,
        "upper": 93.04666666666238,
        "exact": null
      }
    },
    {
      "id": "sol-6.2-xhigh",
      "label": "Sol 6.2 (xhigh)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 83.23333333333333,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 74.16190476190476,
        "upper": 84.16190476190476,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 84.11038095238095,
          "upper": 94.11038095238095,
          "exact": null
        },
        "RMC": {
          "lower": 82.89609523809524,
          "upper": 92.89609523809524,
          "exact": null
        },
        "SMC": {
          "lower": 74.16190476190476,
          "upper": 84.16190476190476,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 84.11038095238095,
        "RMC": 82.89609523809524,
        "SMC": 74.16190476190476
      },
      "strict_confirmed": 74.16190476190476,
      "composite": {
        "lower": 82.89609523809524,
        "upper": 92.89609523809524,
        "exact": null
      }
    },
    {
      "id": "astra-6-xhigh",
      "label": "Astra 6 (xhigh)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 81.33333333333333,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 73.04761904762762,
        "upper": 83.04761904762762,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 83.04092477570683,
          "upper": 93.04092477570683,
          "exact": null
        },
        "RMC": {
          "lower": 82.18378191857683,
          "upper": 92.18378191857683,
          "exact": null
        },
        "SMC": {
          "lower": 73.04761904762762,
          "upper": 83.04761904762762,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 83.04092477570683,
        "RMC": 82.18378191857683,
        "SMC": 73.04761904762762
      },
      "strict_confirmed": 73.04761904762762,
      "composite": {
        "lower": 82.18378191857683,
        "upper": 92.18378191857683,
        "exact": null
      }
    },
    {
      "id": "sol-6.1-xhigh",
      "label": "Sol 6.1 (xhigh)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 70.5,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 63.285714285714285,
        "upper": 73.28571428571429,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 82.44396135264793,
          "upper": 92.44396135264793,
          "exact": null
        },
        "RMC": {
          "lower": 80.44396135265794,
          "upper": 90.44396135265794,
          "exact": null
        },
        "SMC": {
          "lower": 63.285714285714285,
          "upper": 73.28571428571429,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 82.44396135264793,
        "RMC": 80.44396135265794,
        "SMC": 63.285714285714285
      },
      "strict_confirmed": 63.285714285714285,
      "composite": {
        "lower": 80.44396135265794,
        "upper": 90.44396135265794,
        "exact": null
      }
    },
    {
      "id": "terra-6.1-max",
      "label": "Terra 6.1 (max)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 68.63333333333334,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 61.41904761904762,
        "upper": 71.41904761904762,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 74.93972670807571,
          "upper": 84.93972670807571,
          "exact": null
        },
        "RMC": {
          "lower": 73.29324022159571,
          "upper": 83.29324022159571,
          "exact": null
        },
        "SMC": {
          "lower": 61.41904761904762,
          "upper": 71.41904761904762,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 74.93972670807571,
        "RMC": 73.29324022159571,
        "SMC": 61.41904761904762
      },
      "strict_confirmed": 61.41904761904762,
      "composite": {
        "lower": 73.29324022159571,
        "upper": 83.29324022159571,
        "exact": null
      }
    },
    {
      "id": "terra-6.1-xhigh",
      "label": "Terra 6.1 (xhigh)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 64.75,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 58.49999999998714,
        "upper": 68.49999999998714,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 73.16843979969381,
          "upper": 83.16843979969381,
          "exact": null
        },
        "RMC": {
          "lower": 71.97320170445572,
          "upper": 81.97320170445572,
          "exact": null
        },
        "SMC": {
          "lower": 58.49999999998714,
          "upper": 68.49999999998714,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 73.16843979969381,
        "RMC": 71.97320170445572,
        "SMC": 58.49999999998714
      },
      "strict_confirmed": 58.49999999998714,
      "composite": {
        "lower": 71.97320170445572,
        "upper": 81.97320170445572,
        "exact": null
      }
    },
    {
      "id": "claude-opus-5.5-max",
      "label": "Claude Opus 5.5 (max)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 62.483333333333334,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 56.042857142865714,
        "upper": 66.04285714286571,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 85.38069047618762,
          "upper": 95.38069047618762,
          "exact": null
        },
        "RMC": {
          "lower": 83.37592857142572,
          "upper": 93.37592857142572,
          "exact": null
        },
        "SMC": {
          "lower": 56.042857142865714,
          "upper": 66.04285714286571,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 85.38069047618762,
        "RMC": 83.37592857142572,
        "SMC": 56.042857142865714
      },
      "strict_confirmed": 56.042857142865714,
      "composite": {
        "lower": 83.37592857142572,
        "upper": 93.37592857142572,
        "exact": null
      }
    },
    {
      "id": "gemini-4-neon-xhigh",
      "label": "Gemini 4 Neon (xhigh)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 61.166666666666664,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 53.78571428570143,
        "upper": 63.78571428570143,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 83.85842857143714,
          "upper": 93.85842857143714,
          "exact": null
        },
        "RMC": {
          "lower": 77.89628571429,
          "upper": 87.89628571429,
          "exact": null
        },
        "SMC": {
          "lower": 53.78571428570143,
          "upper": 63.78571428570143,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 83.85842857143714,
        "RMC": 77.89628571429,
        "SMC": 53.78571428570143
      },
      "strict_confirmed": 53.78571428570143,
      "composite": {
        "lower": 77.89628571429,
        "upper": 87.89628571429,
        "exact": null
      }
    },
    {
      "id": "claude-sonnet-5.5-max",
      "label": "Claude Sonnet 5.5 (max)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 58.983333333333334,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 52.471428571437144,
        "upper": 62.471428571437144,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 83.53063492062921,
          "upper": 93.53063492062921,
          "exact": null
        },
        "RMC": {
          "lower": 80.19206349205777,
          "upper": 90.19206349205777,
          "exact": null
        },
        "SMC": {
          "lower": 52.471428571437144,
          "upper": 62.471428571437144,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 83.53063492062921,
        "RMC": 80.19206349205777,
        "SMC": 52.471428571437144
      },
      "strict_confirmed": 52.471428571437144,
      "composite": {
        "lower": 80.19206349205777,
        "upper": 90.19206349205777,
        "exact": null
      }
    },
    {
      "id": "claude-opus-5.5-xhigh",
      "label": "Claude Opus 5.5 (xHigh)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 57.21666666666667,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 50.609523809532384,
        "upper": 60.609523809532384,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 82.82122222221079,
          "upper": 92.82122222221079,
          "exact": null
        },
        "RMC": {
          "lower": 80.66336507935365,
          "upper": 90.66336507935365,
          "exact": null
        },
        "SMC": {
          "lower": 50.609523809532384,
          "upper": 60.609523809532384,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 82.82122222221079,
        "RMC": 80.66336507935365,
        "SMC": 50.609523809532384
      },
      "strict_confirmed": 50.609523809532384,
      "composite": {
        "lower": 80.66336507935365,
        "upper": 90.66336507935365,
        "exact": null
      }
    },
    {
      "id": "gemini-4-hydrogen-xhigh",
      "label": "Gemini 4 Hydrogen (xhigh)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 48.25,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 43.07142857142857,
        "upper": 53.07142857142857,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 80.40102380951667,
          "upper": 90.40102380951667,
          "exact": null
        },
        "RMC": {
          "lower": 70.42411904762048,
          "upper": 80.42411904762048,
          "exact": null
        },
        "SMC": {
          "lower": 43.07142857142857,
          "upper": 53.07142857142857,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 80.40102380951667,
        "RMC": 70.42411904762048,
        "SMC": 43.07142857142857
      },
      "strict_confirmed": 43.07142857142857,
      "composite": {
        "lower": 70.42411904762048,
        "upper": 80.42411904762048,
        "exact": null
      }
    },
    {
      "id": "kimi-3.1-pro-max",
      "label": "Kimi 3.1 Pro (max)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 46.38333333333333,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 41.08571428570143,
        "upper": 51.08571428570143,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 68.77659247755969,
          "upper": 78.77659247755969,
          "exact": null
        },
        "RMC": {
          "lower": 64.5694496204154,
          "upper": 74.5694496204154,
          "exact": null
        },
        "SMC": {
          "lower": 41.08571428570143,
          "upper": 51.08571428570143,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 68.77659247755969,
        "RMC": 64.5694496204154,
        "SMC": 41.08571428570143
      },
      "strict_confirmed": 41.08571428570143,
      "composite": {
        "lower": 64.5694496204154,
        "upper": 74.5694496204154,
        "exact": null
      }
    },
    {
      "id": "deepseek-v4.1-flash-1017",
      "label": "DeepSeek v4.1 Flash (max)",
      "kind": "existing-model-unmeasured",
      "delivery": {
        "planned": 45,
        "normal": 0,
        "unknown": 45
      },
      "base_smc": 26.25,
      "components": {
        "autonomy": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "taste": {
          "state": "not-tested",
          "value": null,
          "strict": null
        },
        "capacity": {
          "state": "not-tested",
          "value": null,
          "strict": null
        }
      },
      "task_strict": null,
      "item": {
        "lower": 0.0,
        "upper": 100.0,
        "exact": null
      },
      "coverage": {
        "planned": 1,
        "reviewed": 0,
        "components_planned": 3,
        "components_reviewed": 0
      },
      "strict_overall": {
        "lower": 22.85714285713,
        "upper": 32.85714285713,
        "exact": null
      },
      "composites": {
        "MC": {
          "lower": 69.09324223602857,
          "upper": 79.09324223602857,
          "exact": null
        },
        "RMC": {
          "lower": 57.28849620429111,
          "upper": 67.2884962042911,
          "exact": null
        },
        "SMC": {
          "lower": 22.85714285713,
          "upper": 32.85714285713,
          "exact": null
        }
      },
      "confirmed": {
        "MC": 69.09324223602857,
        "RMC": 57.28849620429111,
        "SMC": 22.85714285713
      },
      "strict_confirmed": 22.85714285713,
      "composite": {
        "lower": 57.28849620429111,
        "upper": 67.2884962042911,
        "exact": null
      }
    }
  ]
};
