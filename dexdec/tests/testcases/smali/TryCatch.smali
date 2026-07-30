.class public LTryCatch;
.super Ljava/lang/Object;
.source "TryCatch.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static divide(II)I
    .registers 2

    .line 5
    :try_start_0
    div-int/2addr p0, p1
    :try_end_1
    .catch Ljava/lang/ArithmeticException; {:try_start_0 .. :try_end_1} :catch_2

    return p0

    .line 6
    :catch_2
    move-exception p0

    .line 7
    const/4 p0, 0x0

    return p0
.end method
