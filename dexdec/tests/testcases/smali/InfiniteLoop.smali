.class public LInfiniteLoop;
.super Ljava/lang/Object;

.field public static LOCK:Ljava/lang/Object;
.field public static counter:I

.method static constructor <clinit>()V
    .registers 1
    new-instance v0, Ljava/lang/Object;
    invoke-direct {v0}, Ljava/lang/Object;-><init>()V
    sput-object v0, LInfiniteLoop;->LOCK:Ljava/lang/Object;
    const/16 v0, 0xa
    sput v0, LInfiniteLoop;->counter:I
    return-void
.end method

.method public static trimToSize(I)V
    .registers 4
    
    sget-object v0, LInfiniteLoop;->LOCK:Ljava/lang/Object;
    
    :loop_start
    monitor-enter v0
    
    :try_start_0
    # break condition: if (counter <= maxSize) break;
    sget v1, LInfiniteLoop;->counter:I
    
    # if counter <= p0, goto break (exit loop)
    if-le v1, p0, :body
    
    # break label actions:
    monitor-exit v0
    :try_end_0
    .catchall {:try_start_0 .. :try_end_0} :catch_all
    return-void

    :body
    :try_start_1
    # body: modify counter
    add-int/lit8 v1, v1, -0x1
    sput v1, LInfiniteLoop;->counter:I
    
    monitor-exit v0
    :try_end_1
    .catchall {:try_start_1 .. :try_end_1} :catch_all
    
    goto :loop_start
    
    :catch_all
    move-exception v1
    monitor-exit v0
    throw v1
.end method
