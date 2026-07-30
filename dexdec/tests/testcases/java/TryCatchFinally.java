// Test case: Try/Catch/Finally
public class TryCatchFinally {
    public static int simpleTryCatch(int x) {
        try {
            if (x == 0) {
                throw new RuntimeException();
            }
            return 1;
        } catch (RuntimeException e) {
            return -1;
        }
    }
}
