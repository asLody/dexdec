.class public LSynchronized;
.super Ljava/lang/Object;
.source "Synchronized.java"


# static fields
.field private static counter:I

.field private static lock:Ljava/lang/Object;


# direct methods
.method static constructor <clinit>()V
    .registers 1

    .line 3
    new-instance v0, Ljava/lang/Object;

    invoke-direct {v0}, Ljava/lang/Object;-><init>()V

    sput-object v0, LSynchronized;->lock:Ljava/lang/Object;

    .line 4
    const/4 v0, 0x0

    sput v0, LSynchronized;->counter:I

    return-void
.end method

.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static computeInSync(II)I
    .registers 3

    .line 17
    sget-object v0, LSynchronized;->lock:Ljava/lang/Object;

    monitor-enter v0

    .line 18
    add-int/2addr p0, p1

    .line 19
    :try_start_4
    sput p0, LSynchronized;->counter:I

    .line 20
    monitor-exit v0

    .line 21
    return p0

    .line 20
    :catchall_8
    move-exception p0

    monitor-exit v0
    :try_end_a
    .catchall {:try_start_4 .. :try_end_a} :catchall_8

    throw p0
.end method

.method public static multiExit(II)I
    .registers 3

    .line 104
    sget-object v0, LSynchronized;->lock:Ljava/lang/Object;

    monitor-enter v0

    .line 105
    if-gez p0, :cond_a

    .line 106
    :try_start_5
    monitor-exit v0

    const/4 p0, -0x1

    return p0

    .line 112
    :catchall_8
    move-exception p0

    goto :goto_16

    .line 108
    :cond_a
    if-gez p1, :cond_f

    .line 109
    monitor-exit v0

    const/4 p0, -0x2

    return p0

    .line 111
    :cond_f
    add-int/2addr p0, p1

    sput p0, LSynchronized;->counter:I

    .line 112
    monitor-exit v0
    :try_end_13
    .catchall {:try_start_5 .. :try_end_13} :catchall_8

    .line 113
    sget p0, LSynchronized;->counter:I

    return p0

    .line 112
    :goto_16
    :try_start_16
    monitor-exit v0
    :try_end_17
    .catchall {:try_start_16 .. :try_end_17} :catchall_8

    throw p0
.end method

.method public static nestedSync(Ljava/lang/Object;I)I
    .registers 3

    .line 49
    sget-object v0, LSynchronized;->lock:Ljava/lang/Object;

    monitor-enter v0

    .line 50
    :try_start_3
    monitor-enter p0
    :try_end_4
    .catchall {:try_start_3 .. :try_end_4} :catchall_10

    .line 51
    mul-int/lit8 p1, p1, 0x2

    :try_start_6
    sput p1, LSynchronized;->counter:I

    .line 52
    monitor-exit p0
    :try_end_9
    .catchall {:try_start_6 .. :try_end_9} :catchall_d

    .line 53
    :try_start_9
    monitor-exit v0
    :try_end_a
    .catchall {:try_start_9 .. :try_end_a} :catchall_10

    .line 54
    sget p0, LSynchronized;->counter:I

    return p0

    .line 52
    :catchall_d
    move-exception p1

    :try_start_e
    monitor-exit p0
    :try_end_f
    .catchall {:try_start_e .. :try_end_f} :catchall_d

    :try_start_f
    throw p1

    .line 53
    :catchall_10
    move-exception p0

    monitor-exit v0
    :try_end_12
    .catchall {:try_start_f .. :try_end_12} :catchall_10

    throw p0
.end method

.method public static simpleSync(I)I
    .registers 2

    .line 8
    sget-object v0, LSynchronized;->lock:Ljava/lang/Object;

    monitor-enter v0

    .line 9
    :try_start_3
    sput p0, LSynchronized;->counter:I

    .line 10
    sget p0, LSynchronized;->counter:I

    monitor-exit v0

    return p0

    .line 11
    :catchall_9
    move-exception p0

    monitor-exit v0
    :try_end_b
    .catchall {:try_start_3 .. :try_end_b} :catchall_9

    throw p0
.end method

.method public static declared-synchronized syncMethod(I)I
    .registers 2

    const-class v0, LSynchronized;

    monitor-enter v0

    .line 98
    :try_start_3
    sput p0, LSynchronized;->counter:I

    .line 99
    sget p0, LSynchronized;->counter:I
    :try_end_7
    .catchall {:try_start_3 .. :try_end_7} :catchall_9

    monitor-exit v0

    return p0

    .line 97
    :catchall_9
    move-exception p0

    :try_start_a
    monitor-exit v0
    :try_end_b
    .catchall {:try_start_a .. :try_end_b} :catchall_9

    throw p0
.end method

.method public static syncWithCondition(I)I
    .registers 2

    .line 26
    sget-object v0, LSynchronized;->lock:Ljava/lang/Object;

    monitor-enter v0

    .line 27
    if-lez p0, :cond_8

    .line 28
    :try_start_5
    sput p0, LSynchronized;->counter:I

    goto :goto_b

    .line 30
    :cond_8
    neg-int p0, p0

    sput p0, LSynchronized;->counter:I

    .line 32
    :goto_b
    monitor-exit v0
    :try_end_c
    .catchall {:try_start_5 .. :try_end_c} :catchall_f

    .line 33
    sget p0, LSynchronized;->counter:I

    return p0

    .line 32
    :catchall_f
    move-exception p0

    :try_start_10
    monitor-exit v0
    :try_end_11
    .catchall {:try_start_10 .. :try_end_11} :catchall_f

    throw p0
.end method

.method public static syncWithLoop([I)I
    .registers 5

    .line 59
    nop

    .line 60
    sget-object v0, LSynchronized;->lock:Ljava/lang/Object;

    monitor-enter v0

    .line 61
    const/4 v1, 0x0

    const/4 v2, 0x0

    :goto_6
    :try_start_6
    array-length v3, p0

    if-ge v1, v3, :cond_f

    .line 62
    aget v3, p0, v1

    add-int/2addr v2, v3

    .line 61
    add-int/lit8 v1, v1, 0x1

    goto :goto_6

    .line 64
    :cond_f
    sput v2, LSynchronized;->counter:I

    .line 65
    monitor-exit v0

    .line 66
    return v2

    .line 65
    :catchall_13
    move-exception p0

    monitor-exit v0
    :try_end_15
    .catchall {:try_start_6 .. :try_end_15} :catchall_13

    goto :goto_17

    :goto_16
    throw p0

    :goto_17
    goto :goto_16
.end method

.method public static syncWithReturn(I)I
    .registers 3

    .line 38
    sget-object v0, LSynchronized;->lock:Ljava/lang/Object;

    monitor-enter v0

    .line 39
    if-nez p0, :cond_8

    .line 40
    :try_start_5
    monitor-exit v0

    const/4 p0, -0x1

    return p0

    .line 42
    :cond_8
    const/16 v1, 0x64

    div-int/2addr v1, p0

    sput v1, LSynchronized;->counter:I

    .line 43
    sget p0, LSynchronized;->counter:I

    monitor-exit v0

    return p0

    .line 44
    :catchall_11
    move-exception p0

    monitor-exit v0
    :try_end_13
    .catchall {:try_start_5 .. :try_end_13} :catchall_11

    throw p0
.end method

.method public static syncWithTry(I)I
    .registers 3

    .line 71
    sget-object v0, LSynchronized;->lock:Ljava/lang/Object;

    monitor-enter v0

    .line 73
    const/16 v1, 0x64

    :try_start_5
    div-int/2addr v1, p0

    sput v1, LSynchronized;->counter:I
    :try_end_8
    .catch Ljava/lang/ArithmeticException; {:try_start_5 .. :try_end_8} :catch_b
    .catchall {:try_start_5 .. :try_end_8} :catchall_9

    .line 76
    goto :goto_f

    .line 77
    :catchall_9
    move-exception p0

    goto :goto_13

    .line 74
    :catch_b
    move-exception p0

    .line 75
    const/4 p0, -0x1

    :try_start_d
    sput p0, LSynchronized;->counter:I

    .line 77
    :goto_f
    monitor-exit v0
    :try_end_10
    .catchall {:try_start_d .. :try_end_10} :catchall_9

    .line 78
    sget p0, LSynchronized;->counter:I

    return p0

    .line 77
    :goto_13
    :try_start_13
    monitor-exit v0
    :try_end_14
    .catchall {:try_start_13 .. :try_end_14} :catchall_9

    throw p0
.end method

.method public static tryWithSync(I)I
    .registers 3

    .line 84
    :try_start_0
    sget-object v0, LSynchronized;->lock:Ljava/lang/Object;

    monitor-enter v0
    :try_end_3
    .catch Ljava/lang/RuntimeException; {:try_start_0 .. :try_end_3} :catch_18

    .line 85
    if-eqz p0, :cond_e

    .line 88
    :try_start_5
    sput p0, LSynchronized;->counter:I

    .line 89
    monitor-exit v0
    :try_end_8
    .catchall {:try_start_5 .. :try_end_8} :catchall_c

    .line 92
    nop

    .line 93
    sget p0, LSynchronized;->counter:I

    return p0

    .line 89
    :catchall_c
    move-exception p0

    goto :goto_16

    .line 86
    :cond_e
    :try_start_e
    new-instance p0, Ljava/lang/RuntimeException;

    const-string v1, "zero"

    invoke-direct {p0, v1}, Ljava/lang/RuntimeException;-><init>(Ljava/lang/String;)V

    throw p0

    .line 89
    :goto_16
    monitor-exit v0
    :try_end_17
    .catchall {:try_start_e .. :try_end_17} :catchall_c

    :try_start_17
    throw p0
    :try_end_18
    .catch Ljava/lang/RuntimeException; {:try_start_17 .. :try_end_18} :catch_18

    .line 90
    :catch_18
    move-exception p0

    .line 91
    const/4 p0, -0x1

    return p0
.end method
