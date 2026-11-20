"""Publication eligibility is separate from mathematical scoring and failures."""
import copy


# Explicitly selected publication status, never inferred from low scores.
PUBLICATION_STATUS = {
    'glm-5.3-max': {
        'status': 'partial_test', 'ranked': False,
        'reason': {
            'zh': '规定评测流程未完成，交付覆盖不足；保留已测部分成绩与原始档案。',
            'en': 'The prescribed evaluation was not completed and delivery coverage is insufficient. Partial results and the original archive remain available.',
        },
    },
}


def eligibility(model_id):
    return copy.deepcopy(PUBLICATION_STATUS.get(model_id, {'status': 'listed', 'ranked': True}))


def is_ranked(model):
    return model.get('presentation_eligibility', {}).get('ranked', True) is True


def ranked_models(models):
    return [model for model in models if is_ranked(model)]
