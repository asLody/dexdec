// Test case: Multiple catch blocks
public class MultiCatch {
    public static int process(int a, int b) {
        try {
            if (a < 0) {
                throw new IllegalArgumentException("negative a");
            }
            return a / b;
        } catch (IllegalArgumentException e) {
            return -1;
        } catch (ArithmeticException e) {
            return -2;
        }
    }
}
