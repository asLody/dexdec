public class HardcoreControlFlow {
    // 1. State Machine: Switch in Loop
    public int stateMachine(int[] input) {
        int state = 0;
        int i = 0;
        int result = 0;
        
        while (i < input.length) {
            int val = input[i];
            switch (state) {
                case 0:
                    if (val > 0) {
                        state = 1;
                        result += val;
                    } else if (val < 0) {
                        state = 2;
                    } else {
                        return result; // Early exit
                    }
                    break;
                case 1:
                    if (val == 0) {
                        state = 0;
                    } else {
                        result *= 2;
                        i++; // Skip next
                    }
                    break;
                case 2:
                    result -= val;
                    state = 0;
                    break;
                default:
                    return -1;
            }
            i++;
        }
        return result;
    }

    // 2. Labeled Multi-Level Break/Continue
    public int labeledBreaks(int[][] matrix) {
        int sum = 0;
        outer: for (int i = 0; i < matrix.length; i++) {
            if (matrix[i] == null) continue;
            
            inner: for (int j = 0; j < matrix[i].length; j++) {
                int val = matrix[i][j];
                
                if (val == -1) {
                    break outer;
                }
                if (val == -2) {
                    continue outer;
                }
                if (val == -3) {
                    break inner;
                }
                
                if (val > 100) {
                    for (int k = 0; k < val; k++) {
                        if (k * j > 1000) {
                            sum += k;
                            continue outer; // Deep continue
                        }
                    }
                }
                
                sum += val;
            }
        }
        return sum;
    }
    
    // 3. Exception Spaghetti
    public int exceptionSpaghetti(int a, int b) {
        int res = 0;
        try {
            if (a > 0) {
                try {
                    res = a / b;
                    if (res > 10) return res;
                } catch (ArithmeticException e) {
                    res = -1;
                    throw e; // Rethrow
                } finally {
                    res += 100;
                }
            } else {
                throw new IllegalArgumentException();
            }
        } catch (IllegalArgumentException e) {
            res -= 100;
        } catch (ArithmeticException e) {
           res = -2;
        } finally {
            if (res > 0) {
                return res * 2;
            }
        }
        return res;
    }
    
    // 4. Short Circuit Side Effects
    public boolean complexLogic(int a, int b) {
        if (check(a) || (modify(a) && check(b)) || modify(b)) {
            return true;
        }
        return false;
    }
    
    private boolean check(int x) { return x > 0; }
    private boolean modify(int x) { return x % 2 == 0; }
}
