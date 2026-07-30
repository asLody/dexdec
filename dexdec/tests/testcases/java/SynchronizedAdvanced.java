// Test case: Advanced synchronized patterns
public class SynchronizedAdvanced {
    private static Object lock1 = new Object();
    private static Object lock2 = new Object();
    private static int value = 0;
    
    // Synchronized block with loop break
    public static int syncWithBreak(int[] arr) {
        int result = 0;
        synchronized (lock1) {
            for (int i = 0; i < arr.length; i++) {
                if (arr[i] < 0) {
                    break;
                }
                result += arr[i];
            }
        }
        return result;
    }
    
    // Synchronized block with loop continue
    public static int syncWithContinue(int[] arr) {
        int sum = 0;
        synchronized (lock1) {
            for (int i = 0; i < arr.length; i++) {
                if (arr[i] == 0) {
                    continue;
                }
                sum += arr[i];
            }
        }
        return sum;
    }
    
    // Synchronized block with while loop
    public static int syncWhileLoop(int n) {
        int count = 0;
        synchronized (lock1) {
            while (n > 0) {
                count++;
                n = n / 2;
            }
        }
        return count;
    }
    
    // Multiple synchronized blocks in sequence
    public static int sequentialSync(int a, int b) {
        int x;
        synchronized (lock1) {
            x = a + 1;
        }
        synchronized (lock2) {
            x = x + b;
        }
        return x;
    }
    
    // Synchronized block with try-catch-finally
    public static int syncWithFinally(int x) {
        int result = 0;
        synchronized (lock1) {
            try {
                result = 100 / x;
            } catch (ArithmeticException e) {
                result = -1;
            } finally {
                value = result;
            }
        }
        return result;
    }
    
    // Deep nesting: try inside sync inside loop
    public static int deepNesting(int[] arr) {
        int sum = 0;
        for (int i = 0; i < arr.length; i++) {
            synchronized (lock1) {
                try {
                    sum += 10 / arr[i];
                } catch (ArithmeticException e) {
                    sum -= 1;
                }
            }
        }
        return sum;
    }
    
    // Synchronized with switch
    public static int syncWithSwitch(int cmd) {
        int result;
        synchronized (lock1) {
            switch (cmd) {
                case 1:
                    result = 10;
                    break;
                case 2:
                    result = 20;
                    break;
                case 3:
                    result = 30;
                    break;
                default:
                    result = 0;
            }
        }
        return result;
    }
    
    // Synchronized block with method call
    public static int syncWithCall(int x) {
        synchronized (lock1) {
            return helper(x);
        }
    }
    
    private static int helper(int x) {
        return x * 2;
    }
    
    // Synchronized on this (instance method)
    public int syncOnThis(int x) {
        synchronized (this) {
            value = x;
        }
        return value;
    }
    
    // Synchronized on class literal
    public static int syncOnClass(int x) {
        synchronized (SynchronizedAdvanced.class) {
            value = x;
        }
        return value;
    }
    
    // Synchronized with nested try and multiple catches
    public static int syncMultiCatch(int x) {
        synchronized (lock1) {
            try {
                if (x < 0) {
                    throw new IllegalArgumentException();
                }
                return 100 / x;
            } catch (ArithmeticException e) {
                return -1;
            } catch (IllegalArgumentException e) {
                return -2;
            }
        }
    }
}
