.class public LMultiReturn;
.super Ljava/lang/Object;
.source "MultiReturn.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static abs(I)I
    .registers 1

    .line 43
    if-ltz p0, :cond_3

    .line 44
    return p0

    .line 46
    :cond_3
    neg-int p0, p0

    return p0
.end method

.method public static earlyReturn(I)I
    .registers 1

    .line 5
    if-gez p0, :cond_4

    .line 6
    const/4 p0, -0x1

    return p0

    .line 8
    :cond_4
    if-nez p0, :cond_8

    .line 9
    const/4 p0, 0x0

    return p0

    .line 11
    :cond_8
    const/4 p0, 0x1

    return p0
.end method

.method public static findValue([II)I
    .registers 4

    .line 16
    const/4 v0, 0x0

    .line 17
    :goto_1
    array-length v1, p0

    if-ge v0, v1, :cond_c

    .line 18
    aget v1, p0, v0

    if-ne v1, p1, :cond_9

    .line 19
    return v0

    .line 21
    :cond_9
    add-int/lit8 v0, v0, 0x1

    goto :goto_1

    .line 23
    :cond_c
    const/4 p0, -0x1

    return p0
.end method

.method public static grade(I)Ljava/lang/String;
    .registers 2

    .line 28
    const/16 v0, 0x5a

    if-lt p0, v0, :cond_7

    .line 29
    const-string p0, "A"

    return-object p0

    .line 30
    :cond_7
    const/16 v0, 0x50

    if-lt p0, v0, :cond_e

    .line 31
    const-string p0, "B"

    return-object p0

    .line 32
    :cond_e
    const/16 v0, 0x46

    if-lt p0, v0, :cond_15

    .line 33
    const-string p0, "C"

    return-object p0

    .line 34
    :cond_15
    const/16 v0, 0x3c

    if-lt p0, v0, :cond_1c

    .line 35
    const-string p0, "D"

    return-object p0

    .line 37
    :cond_1c
    const-string p0, "F"

    return-object p0
.end method
