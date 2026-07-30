public class BranchMaze {
    public static int classify(int a, int b, int c) {
        int x;
        if (a > 0 && (b < 0 || c == 0)) {
            x = 1;
        } else if (a == 0 || (b > 0 && c > 0)) {
            x = 2;
        } else {
            x = 3;
        }

        if (x == 2 && (a < b || c < 0)) {
            x = x + 10;
        }

        return x;
    }
}
