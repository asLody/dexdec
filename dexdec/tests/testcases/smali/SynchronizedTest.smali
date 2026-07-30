.class public LSynchronizedTest;
.super Ljava/lang/Object;
.source "SynchronizedTest.java"


# instance fields
.field private count:I

.field private final lock:Ljava/lang/Object;


# direct methods
.method public constructor <init>()V
    .registers 2

    .line 1
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    .line 2
    new-instance v0, Ljava/lang/Object;

    invoke-direct {v0}, Ljava/lang/Object;-><init>()V

    iput-object v0, p0, LSynchronizedTest;->lock:Ljava/lang/Object;

    .line 3
    const/4 v0, 0x0

    iput v0, p0, LSynchronizedTest;->count:I

    return-void
.end method

.method public static declared-synchronized staticSync(I)V
    .registers 1

    const-class p0, LSynchronizedTest;

    monitor-enter p0

    .line 24
    monitor-exit p0

    return-void
.end method


# virtual methods
.method public testSimpleSync()V
    .registers 3

    .line 6
    iget-object v0, p0, LSynchronizedTest;->lock:Ljava/lang/Object;

    monitor-enter v0

    .line 7
    :try_start_3
    iget v1, p0, LSynchronizedTest;->count:I

    add-int/lit8 v1, v1, 0x1

    iput v1, p0, LSynchronizedTest;->count:I

    .line 8
    monitor-exit v0

    .line 9
    return-void

    .line 8
    :catchall_b
    move-exception v1

    monitor-exit v0
    :try_end_d
    .catchall {:try_start_3 .. :try_end_d} :catchall_b

    throw v1
.end method

.method public testSyncWithControlFlow(I)V
    .registers 4

    .line 12
    iget-object v0, p0, LSynchronizedTest;->lock:Ljava/lang/Object;

    monitor-enter v0

    .line 13
    if-lez p1, :cond_b

    .line 14
    :try_start_5
    iget v1, p0, LSynchronizedTest;->count:I

    add-int/2addr v1, p1

    iput v1, p0, LSynchronizedTest;->count:I

    goto :goto_10

    .line 16
    :cond_b
    iget v1, p0, LSynchronizedTest;->count:I

    sub-int/2addr v1, p1

    iput v1, p0, LSynchronizedTest;->count:I

    .line 18
    :goto_10
    monitor-exit v0

    .line 19
    return-void

    .line 18
    :catchall_12
    move-exception p1

    monitor-exit v0
    :try_end_14
    .catchall {:try_start_5 .. :try_end_14} :catchall_12

    throw p1
.end method
