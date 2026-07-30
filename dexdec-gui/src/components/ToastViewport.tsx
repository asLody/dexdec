import { Check, CircleAlert, Info, X } from "lucide-react";

import { useTranslation } from "../i18n";
import { useActivity } from "../state/activity";

export function ToastViewport() {
  const notices = useActivity((state) => state.notices);
  const dismiss = useActivity((state) => state.dismissNotice);
  const { t } = useTranslation();
  if (!notices.length) return null;
  return (
    <div className="toast-viewport" aria-live="polite" aria-atomic="false">
      {notices.map((notice) => (
        <div key={notice.id} className={`toast is-${notice.tone}`} role="status">
          {notice.tone === "success" ? (
            <Check size={13} />
          ) : notice.tone === "error" ? (
            <CircleAlert size={13} />
          ) : (
            <Info size={13} />
          )}
          <span>{notice.message}</span>
          <button
            type="button"
            title={t("status.dismiss")}
            aria-label={t("status.dismiss")}
            onClick={() => dismiss(notice.id)}
          >
            <X size={11} />
          </button>
        </div>
      ))}
    </div>
  );
}
