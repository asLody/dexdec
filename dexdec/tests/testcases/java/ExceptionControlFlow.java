// Test case: Complex exception control flow
public class ExceptionControlFlow {
    // try-catch-finally with return paths
    public static int tryCatchFinally(int a, int b) {
        try {
            if (b == 0) {
                throw new ArithmeticException();
            }
            return a / b;
        } catch (ArithmeticException e) {
            return -1;
        } finally {
            a = a + 1;
        }
    }

    // nested try/catch
    public static int nestedTry(int x) {
        try {
            try {
                if (x < 0) {
                    throw new IllegalArgumentException();
                }
                return 1;
            } catch (IllegalArgumentException e) {
                return 2;
            }
        } catch (RuntimeException e) {
            return 3;
        }
    }

    // try inside loop with continue/break
    public static int tryInLoop(int[] arr) {
        int sum = 0;
        for (int i = 0; i < arr.length; i++) {
            try {
                if (arr[i] == 0) {
                    continue;
                }
                sum += 10 / arr[i];
            } catch (ArithmeticException e) {
                break;
            }
        }
        return sum;
    }

    // finally with visible side effect
    public static int finallySideEffect(int[] arr) {
        try {
            arr[0] = 1;
            return arr[0];
        } finally {
            arr[0] = arr[0] + 1;
        }
    }

    // nested try with finally and outer catch
    public static int nestedTryFinally(int x) {
        int y = 0;
        try {
            try {
                if (x < 0) {
                    throw new IllegalArgumentException();
                }
                y = 1;
            } finally {
                y = y + 10;
            }
        } catch (RuntimeException e) {
            y = 2;
        }
        return y;
    }

    // try/catch/finally inside loop with continue and early return
    public static int tryCatchFinallyWithContinue(int[] arr) {
        int sum = 0;
        for (int i = 0; i < arr.length; i++) {
            try {
                if (arr[i] == 0) {
                    continue;
                }
                sum += 100 / arr[i];
                if (sum > 50) {
                    return sum;
                }
            } catch (ArithmeticException e) {
                sum -= 1;
            } finally {
                sum += 2;
            }
        }
        return sum;
    }
}
