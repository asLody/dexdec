// Test case: Nested if-else
public class NestedIf {
    public static int compare(int a, int b) {
        if (a > b) {
            if (a > 100) {
                return 2;
            } else {
                return 1;
            }
        } else {
            if (b > 100) {
                return -2;
            } else {
                return -1;
            }
        }
    }
}
