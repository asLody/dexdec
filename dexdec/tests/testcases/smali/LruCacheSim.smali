.class public LLruCacheSim;
.super Ljava/lang/Object;

.method public trimToSize(I)V
    .registers 5

    :goto_0
    monitor-enter p0

    :try_start_0
    # Condition 1: The "Exception Path" that was appearing in CFT
    const v0, 0
    if-ltz p1, :cond_exception
    
    # Condition 2: The "Logic Path" that IS MISSING in CFT
    const v1, 10
    if-le p1, v1, :cond_break
    
    # Loop continuation work (missing?)
    add-int/lit8 p1, p1, -1
    monitor-exit p0
    goto :goto_0

    :cond_break
    monitor-exit p0
    :try_end_0
    .catchall {:try_start_0 .. :try_end_0} :catch_all_0

    return-void

    :cond_exception
    :try_start_1
    new-instance v0, Ljava/lang/IllegalStateException;
    invoke-direct {v0}, Ljava/lang/IllegalStateException;-><init>()V
    throw v0
    :try_end_1
    .catchall {:try_start_1 .. :try_end_1} :catch_all_0

    :catch_all_0
    move-exception v0
    monitor-exit p0
    throw v0
.end method
