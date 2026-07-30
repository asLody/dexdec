public class NestedLoopBranches {
    public static int compute(int[] a, int[][] b, int target) {
        int sum = 0;
        for (int i = 0; i < a.length; i++) {
            if (a[i] < 0) {
                continue;
            }
            int[] row = b[i];
            for (int j = 0; j < row.length; j++) {
                int v = row[j];
                if (v == target) {
                    return sum + v;
                }
                if (v % 2 == 0) {
                    continue;
                }
                sum += v;
                if (sum > 1000) {
                    break;
                }
            }
            if (sum > 1000) {
                break;
            }
        }
        return sum;
    }
}
