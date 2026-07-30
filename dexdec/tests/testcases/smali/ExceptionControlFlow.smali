.class public LExceptionControlFlow;
.super Ljava/lang/Object;
.source "ExceptionControlFlow.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static finallySideEffect([I)I
    .registers 5

    .line 52
    const/4 v0, 0x1

    const/4 v1, 0x0

    :try_start_2
    aput v0, p0, v1

    .line 53
    aget v2, p0, v1
    :try_end_6
    .catchall {:try_start_2 .. :try_end_6} :catchall_c

    .line 55
    aget v3, p0, v1

    add-int/2addr v3, v0

    aput v3, p0, v1

    .line 53
    return v2

    .line 55
    :catchall_c
    move-exception v2

    aget v3, p0, v1

    add-int/2addr v3, v0

    aput v3, p0, v1

    .line 56
    throw v2
.end method

.method public static nestedTry(I)I
    .registers 1

    .line 21
    if-ltz p0, :cond_4

    .line 24
    const/4 p0, 0x1

    return p0

    .line 22
    :cond_4
    :try_start_4
    new-instance p0, Ljava/lang/IllegalArgumentException;

    invoke-direct {p0}, Ljava/lang/IllegalArgumentException;-><init>()V

    throw p0
    :try_end_a
    .catch Ljava/lang/IllegalArgumentException; {:try_start_4 .. :try_end_a} :catch_d
    .catch Ljava/lang/RuntimeException; {:try_start_4 .. :try_end_a} :catch_a

    .line 28
    :catch_a
    move-exception p0

    .line 29
    const/4 p0, 0x3

    return p0

    .line 25
    :catch_d
    move-exception p0

    .line 26
    const/4 p0, 0x2

    return p0
.end method

.method public static nestedTryFinally(I)I
    .registers 1

    .line 61
    nop

    .line 64
    if-ltz p0, :cond_9

    .line 67
    nop

    .line 69
    nop

    .line 70
    nop

    .line 73
    const/16 p0, 0xb

    goto :goto_13

    .line 65
    :cond_9
    :try_start_9
    new-instance p0, Ljava/lang/IllegalArgumentException;

    invoke-direct {p0}, Ljava/lang/IllegalArgumentException;-><init>()V

    throw p0
    :try_end_f
    .catchall {:try_start_9 .. :try_end_f} :catchall_f

    .line 69
    :catchall_f
    move-exception p0

    .line 70
    :try_start_10
    throw p0
    :try_end_11
    .catch Ljava/lang/RuntimeException; {:try_start_10 .. :try_end_11} :catch_11

    .line 71
    :catch_11
    move-exception p0

    .line 72
    const/4 p0, 0x2

    .line 74
    :goto_13
    return p0
.end method

.method public static tryCatchFinally(II)I
    .registers 2

    .line 6
    if-eqz p1, :cond_5

    .line 9
    :try_start_2
    div-int/2addr p0, p1

    .line 13
    nop

    .line 9
    return p0

    .line 7
    :cond_5
    new-instance p0, Ljava/lang/ArithmeticException;

    invoke-direct {p0}, Ljava/lang/ArithmeticException;-><init>()V

    throw p0
    :try_end_b
    .catch Ljava/lang/ArithmeticException; {:try_start_2 .. :try_end_b} :catch_d
    .catchall {:try_start_2 .. :try_end_b} :catchall_b

    .line 13
    :catchall_b
    move-exception p0

    .line 14
    throw p0

    .line 10
    :catch_d
    move-exception p0

    .line 11
    nop

    .line 13
    nop

    .line 11
    const/4 p0, -0x1

    return p0
.end method

.method public static tryCatchFinallyWithContinue([I)I
    .registers 5

    .line 79
    nop

    .line 80
    const/4 v0, 0x0

    const/4 v1, 0x0

    :goto_3
    array-length v2, p0

    if-ge v0, v2, :cond_25

    .line 82
    :try_start_6
    aget v2, p0, v0

    if-nez v2, :cond_d

    .line 92
    add-int/lit8 v1, v1, 0x2

    .line 83
    goto :goto_22

    .line 85
    :cond_d
    aget v2, p0, v0

    const/16 v3, 0x64

    div-int/2addr v3, v2
    :try_end_12
    .catch Ljava/lang/ArithmeticException; {:try_start_6 .. :try_end_12} :catch_1c
    .catchall {:try_start_6 .. :try_end_12} :catchall_1a

    add-int/2addr v1, v3

    .line 86
    const/16 v2, 0x32

    if-le v1, v2, :cond_1f

    .line 87
    nop

    .line 92
    nop

    .line 87
    return v1

    .line 92
    :catchall_1a
    move-exception p0

    .line 93
    throw p0

    .line 89
    :catch_1c
    move-exception v2

    .line 90
    add-int/lit8 v1, v1, -0x1

    .line 92
    :cond_1f
    add-int/lit8 v1, v1, 0x2

    .line 93
    nop

    .line 80
    :goto_22
    add-int/lit8 v0, v0, 0x1

    goto :goto_3

    .line 95
    :cond_25
    return v1
.end method

.method public static tryInLoop([I)I
    .registers 5

    .line 35
    nop

    .line 36
    const/4 v0, 0x0

    const/4 v1, 0x0

    :goto_3
    array-length v2, p0

    if-ge v0, v2, :cond_17

    .line 38
    :try_start_6
    aget v2, p0, v0

    if-nez v2, :cond_b

    .line 39
    goto :goto_12

    .line 41
    :cond_b
    aget v2, p0, v0

    const/16 v3, 0xa

    div-int/2addr v3, v2
    :try_end_10
    .catch Ljava/lang/ArithmeticException; {:try_start_6 .. :try_end_10} :catch_15

    add-int/2addr v1, v3

    .line 44
    nop

    .line 36
    :goto_12
    add-int/lit8 v0, v0, 0x1

    goto :goto_3

    .line 42
    :catch_15
    move-exception p0

    .line 43
    nop

    .line 46
    :cond_17
    return v1
.end method
