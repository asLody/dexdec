// Test case: Multiple return paths
public class MultiReturn {
    // Early return
    public static int earlyReturn(int x) {
        if (x < 0) {
            return -1;
        }
        if (x == 0) {
            return 0;
        }
        return 1;
    }

    // Return from loop
    public static int findValue(int[] arr, int target) {
        int i = 0;
        while (i < arr.length) {
            if (arr[i] == target) {
                return i;
            }
            i = i + 1;
        }
        return -1;
    }

    // Multiple returns in switch
    public static String grade(int score) {
        if (score >= 90) {
            return "A";
        } else if (score >= 80) {
            return "B";
        } else if (score >= 70) {
            return "C";
        } else if (score >= 60) {
            return "D";
        } else {
            return "F";
        }
    }

    // Ternary-like pattern
    public static int abs(int x) {
        if (x >= 0) {
            return x;
        }
        return -x;
    }
}
