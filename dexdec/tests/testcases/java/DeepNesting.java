// Test case: Deeply nested control structures
public class DeepNesting {
    // 3-level nested if
    public static int classify(int x, int y, int z) {
        int result = 0;
        if (x > 0) {
            if (y > 0) {
                if (z > 0) {
                    result = 1;
                } else {
                    result = 2;
                }
            } else {
                if (z > 0) {
                    result = 3;
                } else {
                    result = 4;
                }
            }
        } else {
            if (y > 0) {
                result = 5;
            } else {
                result = 6;
            }
        }
        return result;
    }

    // Nested loops
    public static int matrixSum(int n, int m) {
        int sum = 0;
        int i = 0;
        while (i < n) {
            int j = 0;
            while (j < m) {
                sum = sum + i * m + j;
                j = j + 1;
            }
            i = i + 1;
        }
        return sum;
    }

    // Loop with nested if
    public static int conditionalSum(int n) {
        int sum = 0;
        int i = 0;
        while (i < n) {
            if (i % 2 == 0) {
                sum = sum + i;
            } else {
                sum = sum - i;
            }
            i = i + 1;
        }
        return sum;
    }
}
