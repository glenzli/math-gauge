import re
from pathlib import Path
s = Path('FreshC003.lean').read_text()
pat = re.compile(r'^(?:theorem|def|noncomputable def|structure) ([A-Za-z_][A-Za-z_0-9]*)', re.M)
matches = list(pat.finditer(s))
names = [m.group(1) for m in matches]
keep = set(names[:17])
keep.update('fiber componentFiber subfamily_zero_iff fiber_intersection fiber_antitone fiber_singleton fiber_all_subset'.split())
keep.update('goodRadius pointRadius uniformRadius zeroMatrix radius_ball_iff radius_subset uniform_subset admissible_radius_le point_radius_witness zero_of_lt_pointRadius point_radius_component fiber_forces_zero composite_fiber_forces_zero uniform_le_point zero_of_lt_uniformRadius positive_output_ge_uniform radius_deficit_witness threshold_ball_fiber colip_gap_point colip_no_point_gap colip_gap_uniform ScaleFamily diameter diameter_mono diameterScales channelType threshold_cases threshold_correspondence scale_threshold_mono zero_threshold_mono scale_domain_mono TotallyBoundedInternal internalNet_text entropyDomain entropyDifference'.split())
chunks = [s[:matches[0].start()]]
for i, m in enumerate(matches):
    if m.group(1) in keep:
        end = matches[i+1].start() if i+1 < len(matches) else s.index('\nend Chapter3Fresh', m.end())
        chunks.append(s[m.start():end])
chunks.append('\nend Chapter3Fresh\n')
Path('CurrentSubmissionC003.lean').write_text(''.join(chunks))
print('kept', len(keep), 'of', len(names), 'first missing:', [n for n in names if n not in keep])
