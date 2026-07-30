// Test case: Simple while loop
public class SimpleLoop {
    public static int sum(int n) {
        int result = 0;
        int i = 0;
        while (i < n) {
            result = result + i;
            i = i + 1;
        }
        return result;
    }
}
