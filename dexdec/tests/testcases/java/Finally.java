// Test case: Try-catch-finally
public class Finally {
    private static int counter = 0;
    
    public static int test(int x) {
        try {
            if (x == 0) {
                throw new RuntimeException("zero");
            }
            return 100 / x;
        } catch (RuntimeException e) {
            return -1;
        } finally {
            counter++;
        }
    }
}
