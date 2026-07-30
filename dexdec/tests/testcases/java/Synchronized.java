// Test case: Synchronized blocks and methods
public class Synchronized {
    private static Object lock = new Object();
    private static int counter = 0;
    
    // Simple synchronized block
    public static int simpleSync(int x) {
        synchronized (lock) {
            counter = x;
            return counter;
        }
    }
    
    // Synchronized block with computation
    public static int computeInSync(int a, int b) {
        int result;
        synchronized (lock) {
            result = a + b;
            counter = result;
        }
        return result;
    }
    
    // Synchronized block with conditional
    public static int syncWithCondition(int x) {
        synchronized (lock) {
            if (x > 0) {
                counter = x;
            } else {
                counter = -x;
            }
        }
        return counter;
    }
    
    // Synchronized block with early return
    public static int syncWithReturn(int x) {
        synchronized (lock) {
            if (x == 0) {
                return -1;
            }
            counter = 100 / x;
            return counter;
        }
    }
    
    // Nested synchronized blocks
    public static int nestedSync(Object lock2, int x) {
        synchronized (lock) {
            synchronized (lock2) {
                counter = x * 2;
            }
        }
        return counter;
    }
    
    // Synchronized block with loop
    public static int syncWithLoop(int[] arr) {
        int sum = 0;
        synchronized (lock) {
            for (int i = 0; i < arr.length; i++) {
                sum += arr[i];
            }
            counter = sum;
        }
        return sum;
    }
    
    // Synchronized block with exception handling
    public static int syncWithTry(int x) {
        synchronized (lock) {
            try {
                counter = 100 / x;
            } catch (ArithmeticException e) {
                counter = -1;
            }
        }
        return counter;
    }
    
    // Synchronized block inside try
    public static int tryWithSync(int x) {
        try {
            synchronized (lock) {
                if (x == 0) {
                    throw new RuntimeException("zero");
                }
                counter = x;
            }
        } catch (RuntimeException e) {
            return -1;
        }
        return counter;
    }
    
    // Synchronized method (whole method is synchronized)
    public static synchronized int syncMethod(int x) {
        counter = x;
        return counter;
    }
    
    // Synchronized block with multiple exit points
    public static int multiExit(int x, int y) {
        synchronized (lock) {
            if (x < 0) {
                return -1;
            }
            if (y < 0) {
                return -2;
            }
            counter = x + y;
        }
        return counter;
    }
}
