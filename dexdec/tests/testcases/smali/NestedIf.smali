.class public LNestedIf;
.super Ljava/lang/Object;
.source "NestedIf.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static compare(II)I
    .registers 3

    .line 4
    const/16 v0, 0x64

    if-le p0, p1, :cond_a

    .line 5
    if-le p0, v0, :cond_8

    .line 6
    const/4 p0, 0x2

    return p0

    .line 8
    :cond_8
    const/4 p0, 0x1

    return p0

    .line 11
    :cond_a
    if-le p1, v0, :cond_e

    .line 12
    const/4 p0, -0x2

    return p0

    .line 14
    :cond_e
    const/4 p0, -0x1

    return p0
.end method
