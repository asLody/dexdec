// Test case: Do-while loop
public class DoWhile {
    public static int countDigits(int n) {
        int count = 0;
        do {
            count++;
            n = n / 10;
        } while (n > 0);
        return count;
    }
}
