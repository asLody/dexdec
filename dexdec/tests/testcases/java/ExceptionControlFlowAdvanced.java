// Test case: Advanced exception control flow
public class ExceptionControlFlowAdvanced {
    // multi-catch with finally and looped arithmetic
    public static int multiCatchAndFinally(int[] arr) {
        int sum = 0;
        try {
            for (int i = 0; i < arr.length; i++) {
                if (arr[i] < 0) {
                    throw new IllegalArgumentException();
                }
                sum += 10 / arr[i];
            }
        } catch (IllegalArgumentException e) {
            sum = -2;
        } catch (ArithmeticException e) {
            sum = -1;
        } finally {
            sum += 3;
        }
        return sum;
    }

    // try/catch with nested try inside catch
    public static int nestedTryInCatch(int x) {
        int y = 0;
        try {
            if (x == 0) {
                throw new RuntimeException();
            }
            y = 1;
        } catch (RuntimeException e) {
            try {
                if (x < 0) {
                    throw new IllegalStateException();
                }
                y = 2;
            } catch (IllegalStateException e2) {
                y = 3;
            }
        }
        return y;
    }

    // finally with break and continue in loop
    public static int finallyWithBreakContinue(int[] arr) {
        int sum = 0;
        for (int i = 0; i < arr.length; i++) {
            try {
                if (arr[i] == 0) {
                    continue;
                }
                if (arr[i] < 0) {
                    break;
                }
                sum += arr[i];
            } finally {
                sum += 1;
            }
        }
        return sum;
    }
}
