// Test case: Short-circuit boolean evaluation
public class ShortCircuit {
    // Short-circuit AND
    public static boolean checkAnd(int x, int y) {
        if (x > 0 && y > 0) {
            return true;
        }
        return false;
    }

    // Short-circuit OR
    public static boolean checkOr(int x, int y) {
        if (x > 0 || y > 0) {
            return true;
        }
        return false;
    }

    // Complex short-circuit: (a && b) || (c && d)
    public static boolean checkComplex(int a, int b, int c, int d) {
        if ((a > 0 && b > 0) || (c > 0 && d > 0)) {
            return true;
        }
        return false;
    }

    // Negated short-circuit: !(a && b)
    public static boolean checkNegated(int x, int y) {
        if (!(x > 0 && y > 0)) {
            return true;
        }
        return false;
    }
}
