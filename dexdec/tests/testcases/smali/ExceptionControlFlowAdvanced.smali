.class public LExceptionControlFlowAdvanced;
.super Ljava/lang/Object;
.source "ExceptionControlFlowAdvanced.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static finallyWithBreakContinue([I)I
    .registers 4

    .line 46
    nop

    .line 47
    const/4 v0, 0x0

    const/4 v1, 0x0

    :goto_3
    array-length v2, p0

    if-ge v0, v2, :cond_1f

    .line 49
    :try_start_6
    aget v2, p0, v0

    if-nez v2, :cond_d

    .line 57
    add-int/lit8 v1, v1, 0x1

    .line 50
    goto :goto_1a

    .line 52
    :cond_d
    aget v2, p0, v0

    if-gez v2, :cond_14

    .line 57
    add-int/lit8 v1, v1, 0x1

    .line 53
    goto :goto_1f

    .line 55
    :cond_14
    aget v2, p0, v0
    :try_end_16
    .catchall {:try_start_6 .. :try_end_16} :catchall_1d

    add-int/2addr v1, v2

    .line 57
    add-int/lit8 v1, v1, 0x1

    .line 58
    nop

    .line 47
    :goto_1a
    add-int/lit8 v0, v0, 0x1

    goto :goto_3

    .line 57
    :catchall_1d
    move-exception p0

    .line 58
    throw p0

    .line 60
    :cond_1f
    :goto_1f
    return v1
.end method

.method public static multiCatchAndFinally([I)I
    .registers 5

    .line 5
    nop

    .line 7
    const/4 v0, 0x0

    const/4 v1, 0x0

    :goto_3
    :try_start_3
    array-length v2, p0

    if-ge v0, v2, :cond_19

    .line 8
    aget v2, p0, v0

    if-ltz v2, :cond_13

    .line 11
    aget v2, p0, v0

    const/16 v3, 0xa

    div-int/2addr v3, v2

    add-int/2addr v1, v3

    .line 7
    add-int/lit8 v0, v0, 0x1

    goto :goto_3

    .line 9
    :cond_13
    new-instance p0, Ljava/lang/IllegalArgumentException;

    invoke-direct {p0}, Ljava/lang/IllegalArgumentException;-><init>()V

    throw p0
    :try_end_19
    .catch Ljava/lang/IllegalArgumentException; {:try_start_3 .. :try_end_19} :catch_23
    .catch Ljava/lang/ArithmeticException; {:try_start_3 .. :try_end_19} :catch_1e
    .catchall {:try_start_3 .. :try_end_19} :catchall_1c

    .line 18
    :cond_19
    add-int/lit8 v1, v1, 0x3

    .line 19
    goto :goto_27

    .line 18
    :catchall_1c
    move-exception p0

    .line 19
    throw p0

    .line 15
    :catch_1e
    move-exception p0

    .line 16
    nop

    .line 18
    nop

    .line 19
    const/4 v1, 0x2

    goto :goto_27

    .line 13
    :catch_23
    move-exception p0

    .line 14
    nop

    .line 18
    nop

    .line 19
    const/4 v1, 0x1

    .line 20
    :goto_27
    return v1
.end method

.method public static nestedTryInCatch(I)I
    .registers 2

    .line 25
    nop

    .line 27
    if-eqz p0, :cond_6

    .line 30
    nop

    .line 40
    const/4 p0, 0x1

    goto :goto_1a

    .line 28
    :cond_6
    :try_start_6
    new-instance v0, Ljava/lang/RuntimeException;

    invoke-direct {v0}, Ljava/lang/RuntimeException;-><init>()V

    throw v0
    :try_end_c
    .catch Ljava/lang/RuntimeException; {:try_start_6 .. :try_end_c} :catch_c

    .line 31
    :catch_c
    move-exception v0

    .line 33
    if-ltz p0, :cond_12

    .line 36
    nop

    .line 39
    const/4 p0, 0x2

    goto :goto_1a

    .line 34
    :cond_12
    :try_start_12
    new-instance p0, Ljava/lang/IllegalStateException;

    invoke-direct {p0}, Ljava/lang/IllegalStateException;-><init>()V

    throw p0
    :try_end_18
    .catch Ljava/lang/IllegalStateException; {:try_start_12 .. :try_end_18} :catch_18

    .line 37
    :catch_18
    move-exception p0

    .line 38
    const/4 p0, 0x3

    .line 41
    :goto_1a
    return p0
.end method
