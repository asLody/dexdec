.class public final LPlatformConstants;
.super Ljava/lang/Object;
.source "PlatformConstants.java"

.method public static launch(Landroid/app/Activity;Landroid/content/Intent;)V
    .registers 3

    const v0, 0x14000000
    invoke-virtual {p1, v0}, Landroid/content/Intent;->setFlags(I)Landroid/content/Intent;

    const/4 v0, -0x1
    invoke-virtual {p0, p1, v0}, Landroid/app/Activity;->startActivityForResult(Landroid/content/Intent;I)V

    return-void
.end method

.method public static orient(Landroid/app/Activity;)V
    .registers 2

    const/4 v0, 0x1
    invoke-virtual {p0, v0}, Landroid/app/Activity;->setRequestedOrientation(I)V

    return-void
.end method
