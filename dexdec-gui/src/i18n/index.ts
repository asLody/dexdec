import { create } from "zustand";

import { en, zh, type MessageKey } from "./messages";

export type { MessageKey };

export type Locale = "en" | "zh";
export type LocalePreference = "system" | Locale;

export interface LocaleOption {
  id: Locale;
  label: string;
  documentLanguage: string;
}

export const LOCALES: readonly LocaleOption[] = [
  { id: "en", label: "English", documentLanguage: "en" },
  { id: "zh", label: "中文", documentLanguage: "zh-CN" },
];

const STORAGE_KEY = "dexdec.locale";

function systemLocale(): Locale {
  return (navigator.language || "en").toLowerCase().startsWith("zh") ? "zh" : "en";
}

function loadLocalePreference(): LocalePreference {
  try {
    const stored = localStorage.getItem(STORAGE_KEY);
    if (stored === "system" || stored === "en" || stored === "zh") {
      return stored;
    }
  } catch {
    /* storage unavailable */
  }
  return "system";
}

function resolveLocale(preference: LocalePreference): Locale {
  return preference === "system" ? systemLocale() : preference;
}

interface LocaleState {
  preference: LocalePreference;
  locale: Locale;
  setPreference: (preference: LocalePreference) => void;
}

const initialPreference = loadLocalePreference();

const useLocaleStore = create<LocaleState>((set) => ({
  preference: initialPreference,
  locale: resolveLocale(initialPreference),
  setPreference: (preference) => {
    try {
      localStorage.setItem(STORAGE_KEY, preference);
    } catch {
      /* storage unavailable */
    }
    set({ preference, locale: resolveLocale(preference) });
  },
}));

function translate(locale: Locale, key: MessageKey, args: (string | number)[]): string {
  const dictionary = locale === "zh" ? zh : en;
  let message: string = dictionary[key] ?? en[key] ?? key;
  args.forEach((arg, index) => {
    message = message.replaceAll(`{${index}}`, String(arg));
  });
  return message;
}

export function useTranslation() {
  const localePreference = useLocaleStore((state) => state.preference);
  const locale = useLocaleStore((state) => state.locale);
  const setLocalePreference = useLocaleStore((state) => state.setPreference);
  return {
    locale,
    localePreference,
    setLocalePreference,
    t: (key: MessageKey, ...args: (string | number)[]) => translate(locale, key, args),
  };
}

/** Non-hook access for store actions and other non-component code. */
export function t(key: MessageKey, ...args: (string | number)[]): string {
  return translate(useLocaleStore.getState().locale, key, args);
}

/* Keep <html lang> in sync for font shaping and accessibility. */
const syncDocumentLang = (locale: Locale) => {
  document.documentElement.lang =
    LOCALES.find((option) => option.id === locale)?.documentLanguage ?? "en";
};
syncDocumentLang(useLocaleStore.getState().locale);
useLocaleStore.subscribe((state) => syncDocumentLang(state.locale));

window.addEventListener("languagechange", () => {
  const state = useLocaleStore.getState();
  if (state.preference === "system") {
    useLocaleStore.setState({ locale: systemLocale() });
  }
});
