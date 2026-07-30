// Test case: Complex switch statements
public class ComplexSwitch {
    // Switch with fall-through
    public static int categorize(int n) {
        int result;
        switch (n) {
            case 1:
            case 2:
            case 3:
                result = 1; // small
                break;
            case 4:
            case 5:
                result = 2; // medium
                break;
            default:
                result = 3; // large
                break;
        }
        return result;
    }

    // Switch with return in cases
    public static String dayName(int day) {
        switch (day) {
            case 1:
                return "Monday";
            case 2:
                return "Tuesday";
            case 3:
                return "Wednesday";
            case 4:
                return "Thursday";
            case 5:
                return "Friday";
            case 6:
                return "Saturday";
            case 7:
                return "Sunday";
            default:
                return "Invalid";
        }
    }

    // Nested switch
    public static int nestedSwitch(int a, int b) {
        int result = 0;
        switch (a) {
            case 1:
                switch (b) {
                    case 1:
                        result = 11;
                        break;
                    case 2:
                        result = 12;
                        break;
                    default:
                        result = 10;
                        break;
                }
                break;
            case 2:
                result = 20;
                break;
            default:
                result = 0;
                break;
        }
        return result;
    }
}
