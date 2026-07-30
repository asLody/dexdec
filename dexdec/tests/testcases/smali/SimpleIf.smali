.class public LSimpleIf;
.super Ljava/lang/Object;
.source "SimpleIf.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static test(I)I
    .registers 1

    .line 4
    if-lez p0, :cond_4

    .line 5
    const/4 p0, 0x1

    return p0

    .line 7
    :cond_4
    const/4 p0, -0x1

    return p0
.end method
