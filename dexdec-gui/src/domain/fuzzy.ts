/*
 * Subsequence fuzzy match with bonuses for consecutive hits and matches at
 * segment boundaries (after `.`, `$`, `/`, `(`, or at the start). Returns
 * null when the query is not a subsequence of the candidate.
 */
export function fuzzyMatch(
  query: string,
  text: string,
): { score: number; indices: number[] } | null {
  const needle = query.toLocaleLowerCase();
  const haystack = text.toLocaleLowerCase();
  const indices: number[] = [];
  let score = 0;
  let cursor = 0;
  let previous = -2;
  for (const char of needle) {
    const found = haystack.indexOf(char, cursor);
    if (found === -1) {
      return null;
    }
    if (found === previous + 1) {
      score += 6;
    } else if (found === 0 || ".$/(".includes(haystack[found - 1])) {
      score += 4;
    } else {
      score += 1;
    }
    indices.push(found);
    previous = found;
    cursor = found + 1;
  }
  score -= text.length * 0.01;
  return { score, indices };
}
