.class public LMultiCatch;
.super Ljava/lang/Object;
.source "MultiCatch.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static process(II)I
    .registers 2

    .line 5
    if-ltz p0, :cond_4

    .line 8
    :try_start_2
    div-int/2addr p0, p1

    return p0

    .line 6
    :cond_4
    new-instance p0, Ljava/lang/IllegalArgumentException;

    const-string p1, "negative a"

    invoke-direct {p0, p1}, Ljava/lang/IllegalArgumentException;-><init>(Ljava/lang/String;)V

    throw p0
    :try_end_c
    .catch Ljava/lang/IllegalArgumentException; {:try_start_2 .. :try_end_c} :catch_f
    .catch Ljava/lang/ArithmeticException; {:try_start_2 .. :try_end_c} :catch_c

    .line 11
    :catch_c
    move-exception p0

    .line 12
    const/4 p0, -0x2

    return p0

    .line 9
    :catch_f
    move-exception p0

    .line 10
    const/4 p0, -0x1

    return p0
.end method
