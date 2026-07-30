// Test case: Complex loops and control flow
public class ComplexControlFlow {
    // For-loop with continue and break
    public static int sumUntil(int[] arr, int limit) {
        int sum = 0;
        for (int i = 0; i < arr.length; i++) {
            int v = arr[i];
            if (v < 0) {
                continue;
            }
            sum = sum + v;
            if (sum > limit) {
                break;
            }
        }
        return sum;
    }

    // Nested loops with early return and inner break
    public static int findInMatrix(int[][] m, int target) {
        for (int i = 0; i < m.length; i++) {
            int[] row = m[i];
            for (int j = 0; j < row.length; j++) {
                if (row[j] == target) {
                    return i * 1000 + j;
                }
                if (row[j] == -1) {
                    break;
                }
            }
        }
        return -1;
    }

    // While loop with switch and control flow
    public static int whileSwitch(int x) {
        int sum = 0;
        int i = 0;
        while (i < 5) {
            switch (x + i) {
                case 0:
                    sum = sum + 1;
                    break;
                case 1:
                    sum = sum + 2;
                    break;
                case 2:
                    sum = sum + 3;
                    break;
                default:
                    sum = sum + 4;
                    break;
            }
            if (sum > 6) {
                i = i + 1;
                continue;
            }
            if (sum > 10) {
                break;
            }
            i = i + 1;
        }
        return sum;
    }

    // Do-while with clamp and break
    public static int doWhileClamp(int x) {
        int v = x;
        do {
            if (v < 0) {
                v = -v;
            }
            if (v > 10) {
                v = 10;
                break;
            }
            v = v + 1;
        } while (v < 5);
        return v;
    }
}
