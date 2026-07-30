.class public LConstructorDelegate;
.super Ljava/lang/Number;
.source "ConstructorDelegate.java"


# direct methods
.method public constructor <init>(I)V
    .registers 2

    .line 2
    invoke-direct {p0, p1}, Ljava/lang/Number;-><init>(I)V

    return-void
.end method

.method public doubleValue()D
    .registers 2

    const-wide/16 v0, 0x0

    return-wide v0
.end method

.method public floatValue()F
    .registers 1

    const/4 v0, 0x0

    return v0
.end method

.method public intValue()I
    .registers 1

    const/4 v0, 0x0

    return v0
.end method

.method public longValue()J
    .registers 2

    const-wide/16 v0, 0x0

    return-wide v0
.end method
