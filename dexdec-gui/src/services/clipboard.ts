import { t } from "../i18n";
import { ActivityCenter } from "../state/activity";

/** Clipboard write with a legacy fallback for non-secure contexts. */
export async function copyText(text: string): Promise<boolean> {
  try {
    await navigator.clipboard.writeText(text);
    ActivityCenter.notify(t("toast.copied"), "success");
    return true;
  } catch {
    try {
      const area = document.createElement("textarea");
      area.value = text;
      area.style.position = "fixed";
      area.style.opacity = "0";
      document.body.appendChild(area);
      area.select();
      const ok = document.execCommand("copy");
      area.remove();
      ActivityCenter.notify(
        t(ok ? "toast.copied" : "toast.copyFailed"),
        ok ? "success" : "error",
      );
      return ok;
    } catch {
      ActivityCenter.notify(t("toast.copyFailed"), "error");
      return false;
    }
  }
}
