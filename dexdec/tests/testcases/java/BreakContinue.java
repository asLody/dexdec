// Test case: Break and Continue in loops
public class BreakContinue {
    // Simple break in while loop
    public static int findFirst(int[] arr, int target) {
        int i = 0;
        int result = -1;
        while (i < arr.length) {
            if (arr[i] == target) {
                result = i;
                break;
            }
            i = i + 1;
        }
        return result;
    }

    // Continue in loop
    public static int sumPositive(int[] arr) {
        int sum = 0;
        int i = 0;
        while (i < arr.length) {
            if (arr[i] <= 0) {
                i = i + 1;
                continue;
            }
            sum = sum + arr[i];
            i = i + 1;
        }
        return sum;
    }

    // Nested loops with break
    public static boolean findPair(int[] arr, int target) {
        int i = 0;
        while (i < arr.length) {
            int j = i + 1;
            while (j < arr.length) {
                if (arr[i] + arr[j] == target) {
                    return true;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        return false;
    }
}
